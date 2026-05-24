from __future__ import (absolute_import, division,
        print_function, unicode_literals)

from collections import defaultdict
from math import sqrt, atan2, degrees, sin, cos, radians, pi, hypot
import traceback
import FreeCAD
import FreeCADGui
import Part
from FreeCAD import Console, Vector, Placement, Rotation
import DraftGeomUtils, DraftVecUtils
import Path

import sys, os
import re
sys.path.append(os.path.dirname(os.path.realpath(__file__)))
from .kicad_parser import KicadPCB, SexpList, SexpParser, parseSexp
from .kicad_parser import unquote

PY3 = sys.version_info[0] == 3
if PY3:
    string_types = str,
else:
    string_types = basestring,

_hasElementMapping = hasattr(Part, 'disableElementMapping')

def disableTopoNaming(obj, enable=True):
    if _hasElementMapping:
        if isinstance(obj, FreeCAD.DocumentObject):
            Part.disableElementMapping(obj, enable)
        else:
            obj.Tag = -1 if enable else 0
    return obj

def addObject(doc, tp, name):
    obj = doc.addObject(tp, name)
    disableTopoNaming(obj)
    try:
        obj.ValidateShape = False
        obj.FixShape = 0
    except Exception:
        pass
    return obj

def setObjectLinks(obj, links, objs):
    if not _hasElementMapping or not objs:
        setattr(obj, links, objs)
        return

    if not isinstance(objs, (list, tuple)):
        objlist = [objs,]
    else:
        objlist = objs

    color = None
    if isinstance(objlist[0], FreeCAD.DocumentObject):
        color = objlist[0].ViewObject.DiffuseColor
        for o in objlist[1:]:
            if o.ViewObject.DiffuseColor != color:
                for o in objlist:
                    disableTopoNaming(o, False)
                disableTopoNaming(obj, False)
                colors = None
                break
    setattr(obj, links, objs)
    if color:
        obj.ViewObject.DiffuseColor = color

def updateGui():
    try:
        FreeCADGui.updateGui()
    except Exception:
        pass

class FCADLogger:
    def __init__(self, tag):
        self.tag = tag
        self.levels = { 'error': 0, 'warning': 1, 'info': 2, 'log': 3, 'trace': 4 }

    def _isEnabledFor(self, level):
        return FreeCAD.getLogLevel(self.tag) >= level

    def isEnabledFor(self, level):
        return self._isEnabledFor(self.levels[level])

    def trace(self, msg):
        if self._isEnabledFor(4):
            FreeCAD.Console.PrintLog(msg + '\n')
            updateGui()

    def log(self, msg):
        if self._isEnabledFor(3):
            FreeCAD.Console.PrintLog(msg + '\n')
            updateGui()

    def info(self, msg):
        if self._isEnabledFor(2):
            FreeCAD.Console.PrintMessage(msg + '\n')
            updateGui()

    def warning(self, msg):
        if self._isEnabledFor(1):
            FreeCAD.Console.PrintWarning(msg + '\n')
            updateGui()

    def error(self, msg):
        if self._isEnabledFor(0):
            FreeCAD.Console.PrintError(msg + '\n')
            updateGui()

logger = FCADLogger('fcad_pcb')

def getActiveDoc():
    if FreeCAD.ActiveDocument is None:
        return FreeCAD.newDocument('kicad_fcad')
    return FreeCAD.ActiveDocument

def fitView():
    try:
        FreeCADGui.ActiveDocument.ActiveView.fitAll()
    except Exception:
        pass

def isZero(f):
    return round(f, DraftGeomUtils.precision()) == 0

def makeColor(*color):
    if len(color) == 1:
        if isinstance(color[0], string_types):
            color = int(color[0], 0)
        else:
            color = color[0]
        r = float((color >> 24) & 0xFF)
        g = float((color >> 16) & 0xFF)
        b = float((color >> 8) & 0xFF)
    else:
        r, g, b = color
    return (r / 255.0, g / 255.0, b / 255.0)

def makeVect(l):
    return Vector(l[0], -l[1], 0)

def getAt(sexp):
    at = getattr(sexp, 'at', None)
    if not at:
        return Vector(0, 0, 0), 0
    v = makeVect(at)
    return (v, 0) if len(at) == 2 else (v, at[2])

def product(v1, v2):
    return Vector(v1.x * v2.x, v1.y * v2.y, v1.z * v2.z)

def make_rect(size, params=None):
    _ = params
    return Part.makePolygon([product(size, Vector(*v))
        for v in ((-0.5, -0.5), (0.5, -0.5), (0.5, 0.5), (-0.5, 0.5), (-0.5, -0.5))])

def make_trapezoid(size, params):
    pts = [product(size, Vector(*v)) for v in ((-0.5, 0.5), (-0.5, -0.5), (0.5, -0.5), (0.5, 0.5))]
    try:
        delta = params.rect_delta[0]
        if delta:
            idx = 1
            length = size[1]
        else:
            delta = params.rect_delta[1]
            idx = 0
            length = size[0]
        if delta <= -length:
            collapse = 1
            delta = -length
        elif delta >= length:
            collapse = -1
            delta = length
        else:
            collapse = 0
        pts[0][idx] += delta * 0.5
        pts[1][idx] -= delta * 0.5
        pts[2][idx] += delta * 0.5
        pts[3][idx] -= delta * 0.5
        if collapse:
            del pts[collapse]
    except Exception:
        logger.warning('trapezoid pad has no rect_delta')

    pts.append(pts[0])
    return Part.makePolygon(pts)

def make_circle(size, params=None):
    _ = params
    return Part.Wire(Part.makeCircle(size.x * 0.5))

def make_oval(size, params=None):
    _ = params
    if size.x == size.y:
        return make_circle(size)
    if size.x < size.y:
        r = size.x * 0.5
        size.y -= size.x
        s = ((0, 0.5), (-0.5, 0.5), (-0.5, -0.5), (0, -0.5), (0.5, -0.5), (0.5, 0.5))
        a = (0, 180, 180, 360)
    else:
        r = size.y * 0.5
        size.x -= size.y
        s = ((-0.5, 0), (-0.5, -0.5), (0.5, -0.5), (0.5, 0), (0.5, 0.5), (-0.5, 0.5))
        a = (90, 270, -90, -270)
    pts = [product(size, Vector(*v)) for v in s]
    return Part.Wire([
            Part.makeCircle(r, pts[0], Vector(0, 0, 1), a[0], a[1]),
            Part.makeLine(pts[1], pts[2]),
            Part.makeCircle(r, pts[3], Vector(0, 0, 1), a[2], a[3]),
            Part.makeLine(pts[4], pts[5])])

def make_roundrect(size, params):
    rratio = 0.25
    try:
        rratio = params.roundrect_rratio
        if rratio > 0.5:
            return make_oval(size)
    except Exception:
        logger.warning('round rect pad has no rratio')

    length = min(size.x, size.y)
    r = length * rratio
    n = Vector(0, 0, 1)
    sx = size.x * 0.5
    sy = size.y * 0.5

    rounds = [(r, False)] * 4

    if 'chamfer_ratio' in params and 'chamfer' in params:
        ratio = params.chamfer_ratio
        if ratio < 0.0:
            ratio = 0.0
        elif ratio > 0.5:
            ratio = 0.5
        for i, corner in enumerate(('top_right', 'top_left', 'bottom_left', 'bottom_right')):
            if corner in params.chamfer:
                rounds[i] = (ratio * length, True)

    edges = []

    r, chamfer = rounds[0]
    pstart = Vector(sx, sy - r)
    pt = pstart
    pnext = Vector(sx - r, sy)

    if r:
        if not chamfer:
            edges.append(Part.makeCircle(r, Vector(sx - r, sy - r), n, 0, 90))
        else:
            edges.append(Part.makeLine(pt, pnext))

    r, chamfer = rounds[1]
    pt = pnext
    pnext = Vector(r - sx, sy)
    if pt != pnext:
        edges.append(Part.makeLine(pt, pnext))
        pt = pnext
    pnext = Vector(-sx, sy - r)

    if r:
        if not chamfer:
            edges.append(Part.makeCircle(r, Vector(r - sx, sy - r), n, 90, 180))
        else:
            edges.append(Part.makeLine(pt, pnext))

    r, chamfer = rounds[2]
    pt = pnext
    pnext = Vector(-sx, r - sy)
    if pt != pnext:
        edges.append(Part.makeLine(pt, pnext))
        pt = pnext
    pnext = Vector(r - sx, -sy)

    if r:
        if not chamfer:
            edges.append(Part.makeCircle(r, Vector(r - sx, r - sy), n, 180, 270))
        else:
            edges.append(Part.makeLine(pt, pnext))

    r, chamfer = rounds[3]
    pt = pnext
    pnext = Vector(sx - r, -sy)
    if pt != pnext:
        edges.append(Part.makeLine(pt, pnext))
        pt = pnext
    pnext = Vector(sx, r - sy)

    if r:
        if not chamfer:
            edges.append(Part.makeCircle(r, Vector(sx - r, r - sy), n, 270, 360))
        else:
            edges.append(Part.makeLine(pt, pnext))

    pt = pnext
    if pt != pstart:
        edges.append(Part.makeLine(pt, pstart))

    return Part.Wire(edges)

def make_gr_poly(params):
    points = SexpList(params.pts.xy)
    points._append(params.pts.xy._get(0))
    poly = Part.makePolygon([makeVect(p) for p in reversed(points)])
    try:
        area = Path.Area(Fill=True, FitArcs=False, Coplanar=0, Outline=True)
        area.add(poly)
        return area.getShape().Wire1
    except Exception as e:
        logger.warning('Failed to get outline of gr_poly: {}'.format(str(e)))
        return poly

def make_gr_line(params):
    return Part.makeLine(makeVect(params.start), makeVect(params.end))

def make_gr_arc(params):
    if hasattr(params, 'angle'):
        return makeArc(makeVect(params.start), makeVect(params.end), params.angle)
    return Part.ArcOfCircle(makeVect(params.start), makeVect(params.mid), makeVect(params.end)).toShape()

def make_gr_curve(params):
    return makeCurve([makeVect(p) for p in SexpList(params.pts.xy)])

def make_gr_circle(params, width=0):
    center = makeVect(params.center)
    end = makeVect(params.end)
    r = center.distanceToPoint(end)
    if not width or r <= width * 0.5:
        return Part.makeCircle(r + width * 0.5, center)
    return Part.makeCompound([Part.Wire(Part.makeCircle(r + width * 0.5, center)),
                              Part.Wire(Part.makeCircle(r - width * 0.5, center, Vector(0, 0, -1)))])

def make_gr_rect(params):
    start = makeVect(params.start)
    end = makeVect(params.end)
    return Part.makePolygon([start, Vector(start.x, end.y), end, Vector(end.x, start.y), start])

def getLineWidth(param, default):
    width = getattr(param, 'width', None)
    if not width:
        if hasattr(param, 'stroke'):
            width = getattr(param.stroke, 'width', default)
        else:
            width = default
    return width

def makePrimitve(key, param):
    try:
        width = getLineWidth(param, 0)
        if width and key == 'gr_circle':
            return make_gr_circle(param, width), 0
        else:
            make_shape = globals()['make_{}'.format(key)]
            return make_shape(param), width
    except KeyError:
        logger.warning('Unknown primitive {} in custom pad'.format(key))
        return None, None

def makeThickLine(p1, p2, width):
    length = p1.distanceToPoint(p2)
    line = make_oval(Vector(length + 2 * width, 2 * width))
    p = p2.sub(p1)
    a = -degrees(DraftVecUtils.angle(p))
    line.translate(Vector(length * 0.5))
    line.rotate(Vector(), Vector(0, 0, 1), a)
    line.translate(p1)
    return line

def makeArc(center, start, angle):
    p = start.sub(center)
    r = p.Length
    a = -degrees(DraftVecUtils.angle(p))
    if angle > 0:
        arc = Part.makeCircle(r, center, Vector(0, 0, 1), a - angle, a)
        arc.reverse()
    else:
        arc = Part.makeCircle(r, center, Vector(0, 0, 1), a, a - angle)
    return arc

def makeCurve(poles):
    return Part.BSplineCurve(poles).toShape()

def findWires(edges):
    try:
        return [Part.Wire(e) for e in Part.sortEdges(edges)]
    except AttributeError:
        msg = 'Missing Part.sortEdges. You need newer FreeCAD (0.17 git 799c43d2)'
        logger.error(msg)
        raise AttributeError(msg)

def getFaceCompound(shape, wire=False):
    objs = []
    for f in shape.Faces:
        selected = True
        for v in f.Vertexes:
            if not isZero(v.Z):
                selected = False
                break
        if not selected:
            continue
        if not wire:
            objs.append(f)
            continue
        for w in f.Wires:
            objs.append(w)
    if not objs:
        raise ValueError('null shape')
    return Part.makeCompound(objs)

def unpack(obj):
    if not obj:
        raise ValueError('null shape')
    if isinstance(obj, (list, tuple)) and len(obj) == 1:
        return obj[0]
    return obj

def getKicadPath(env=''):
    confpath = ''
    if env:
        confpath = os.path.expanduser(os.environ.get(env, ''))
        if not os.path.isdir(confpath):
            confpath = ''
    if not confpath:
        if sys.platform == 'darwin':
            confpath = os.path.expanduser('~/Library/Preferences/kicad')
        elif sys.platform == 'win32':
            confpath = os.path.join(os.path.abspath(os.environ['APPDATA']), 'kicad')
        else:
            confpath = os.path.expanduser('~/.config/kicad')

    kicad_common = os.path.join(confpath, 'kicad_common')
    if not os.path.isfile(kicad_common):
        kicad_common += ".json"
        if not os.path.isfile(kicad_common):
            subdir = None
            version = 0
            for dir in os.listdir(confpath):
                try:
                    if float(dir) > version:
                        version = float(dir)
                        subdir = dir
                except:
                    continue
            if subdir is None or version == 0:
                return None
            confpath = os.path.join(confpath, subdir)
            kicad_common = os.path.join(confpath, 'kicad_common')
            if not os.path.isfile(kicad_common):
                kicad_common += ".json"
                if not os.path.isfile(kicad_common):
                    logger.warning('cannot find kicad_common')
                    return None
    with open(kicad_common, 'r') as f:
        content = f.read()
    match = re.search(r'^\s*"*KISYS3DMOD"*\s*[:=]\s*([^\r\n]+)', content, re.MULTILINE)
    if not match:
        logger.warning('no KISYS3DMOD found')
        return None
    return match.group(1).rstrip(' "')

_model_cache = {}

def clearModelCache():
    global _model_cache
    _model_cache = {}

def recomputeObj(obj):
    obj.recompute()
    obj.purgeTouched()

def loadModel(filename):
    mtime = None
    try:
        mtime = os.path.getmtime(filename)
        obj = _model_cache[filename]
        if obj[2] == mtime:
            logger.info('model cache hit')
            return obj
    except KeyError:
        pass
    except OSError:
        return

    import ImportGui
    doc = getActiveDoc()
    if not os.path.isfile(filename):
        return
    count = len(doc.Objects)
    dobjs = []
    try:
        ImportGui.insert(filename, doc.Name)
        dobjs = doc.Objects[count:]
        obj = addObject(doc, 'Part::Compound', 'tmp')
        setObjectLinks(obj, 'Links', dobjs)
        recomputeObj(obj)
        dobjs = [obj] + dobjs
        obj = (obj.Shape.copy(), obj.ViewObject.DiffuseColor, mtime)
        _model_cache[filename] = obj
        return obj
    except Exception as ex:
        logger.error('failed to load model: {}'.format(ex))
    finally:
        for o in dobjs:
            doc.removeObject(o.Name)

class KicadFcad:
    def __init__(self, filename=None, debug=False, **kwds):
        self.prefix = ''
        self.indent = '  '
        self.make_sketch = False
        self.sketch_use_draft = False
        self.sketch_radius_precision = -1
        self.holes_cache = {}
        self.workplane = {}
        self.active_doc_uuid = None
        self.sketch_constraint = True
        self.sketch_align_constraint = False
        self.merge_holes = not debug
        self.merge_vias = not debug
        self.merge_tracks = not debug
        self.zone_merge_holes = not debug
        self.merge_pads = not debug
        self.castellated = False
        self.refine = False
        self.arc_fit_accuracy = 0.0005
        self.layer_thickness = 0.01
        self.copper_thickness = 0.05
        self.board_thickness = None
        self.stackup = None
        self.quote_no_parse = None

        self.via_bound = 0
        self.via_skip_hole = None

        self.add_feature = True
        self.part_path = None
        self.path_env = 'KICAD_CONFIG_HOME'
        self.hole_size_offset = 0.0001
        self.pad_inflate = 0
        self.zone_inflate = 0
        self.nets = []
        if filename is None:
            filename = 'board.kicad_pcb'
        if not os.path.isfile(filename):
            raise ValueError("file not found")
        self.filename = filename
        self.colors = {
                'board': {0: makeColor("0x3A6629")},
                'pad': {0: makeColor(204, 204, 204)},
                'zone': {0: makeColor(0, 80, 0)},
                'track': {0: makeColor(0, 120, 0)},
                'copper': {0: makeColor(200, 117, 51)},
        }
        self.layer_type = 0
        self.layer_match = None
        self.encoding = 'utf-8'

        for key, value in kwds.items():
            if not hasattr(self, key):
                raise ValueError('unknown parameter "{}"'.format(key))
            setattr(self, key, value)

        if not self.part_path:
            self.part_path = getKicadPath(self.path_env)
        self.pcb = KicadPCB.load(self.filename, self.quote_no_parse, self.encoding)

        if self.pcb._key == 'footprint':
            self.pcb._key = 'module'
        if self.pcb._key == 'module':
            self.module = self.pcb
            board_header = '(kicad_pcb (general (thickness 1.6)) (layers (0 F.Cu signal) (31 B.Cu signal)))'
            self.pcb = KicadPCB(parseSexp(board_header, self.quote_no_parse))
        else:
            self.module = None

        if not self.board_thickness:
            try:
                self.board_thickness = self.pcb.general.thickness
            except Exception:
                pass
            if not self.board_thickness:
                self.board_thickness = 1.6

        self._dielectric_layers = []
        self._stackup_map = {}
        self._initStackUp()

        self.layer_name = ''
        self.layer = ''
        self.setLayer(self.layer_type)

        if self.via_skip_hole is None and self.via_bound:
            self.via_skip_hole = True

        self._nets = set()
        self.net_names = dict()
        if 'net' in self.pcb:
            for n in self.pcb.net:
                self.net_names[n[0]] = n[1]
            self.setNetFilter(*self.nets)

        self.board_face = None
        self.board_uid = None

    def findLayer(self, layer, deftype=None):
        try:
            layer = int(layer)
        except:
            for layer_type in self.pcb.layers:
                name = self.pcb.layers[layer_type][0]
                if name == layer or unquote(name) == layer:
                    return (int(layer_type), name)
            if deftype is not None:
                return deftype, layer
            raise KeyError('layer {} not found'.format(layer))
        else:
            if str(layer) not in self.pcb.layers:
                if deftype is not None:
                    return deftype, str(layer)
                raise KeyError('layer {} not found'.format(layer))
            return (layer, self.pcb.layers[str(layer)][0])

    def setLayer(self, layer):
        self.layer_type, self.layer_name = self.findLayer(layer)
        self.layer = unquote(self.layer_name)
        
        copper_types = [x[0] for x in self._copperLayers()]
        if self.layer_type in copper_types:
            self.layer_match = '*.Cu'
        else:
            self.layer_match = '*.{}'.format(self.layer.split('.')[-1])

    def _copperLayers(self):
        coppers = []
        for t in self.pcb.layers:
            layer_info = self.pcb.layers[t]
            if len(layer_info) > 1:
                ltype = unquote(str(layer_info[1])).strip().lower()
                if ltype in ('signal', 'power', 'mixed', 'jumper'):
                    coppers.append((int(t), unquote(layer_info[0])))
        coppers.sort(key=lambda x: x[0])
        return coppers

    def _initStackUp(self):
        if self.stackup is None:
            self.stackup = []
            stackup = getattr(getattr(self.pcb, 'setup', None), 'stackup', None)
            if stackup:
                try:
                    offset = 0.0
                    last_copper = 0.0
                    copper_types = [x[0] for x in self._copperLayers()]
                    for layer in stackup.layer:
                        layer_type, _ = self.findLayer(layer[0], 99)
                        t = getattr(layer, 'thickness',
                                self.copper_thickness if layer_type in copper_types else self.layer_thickness)
                        if layer_type in copper_types:
                            last_copper = offset
                        if isinstance(t, SexpList):
                            total = 0.0
                            for tt in t:
                                if isinstance(tt, (float, int)):
                                    total += tt
                                else:
                                    total += tt[0]
                            t = total
                        elif not isinstance(t, (float, int)):
                            t = t[0]

                        offset -= t
                        self.stackup.append([unquote(layer[0]), offset, t])

                    for entry in self.stackup:
                        entry[1] -= last_copper
                except Exception as e:
                    self._log('Failed parsing stackup info: {}', str(e), level='warning')

        board_thickness = 0.0
        accumulate = None
        copper_types = [x[0] for x in self._copperLayers()]
        for item in self.stackup:
            layer, name = self.findLayer(item[0], 99)
            self._stackup_map[unquote(name)] = item
            thickness = item[2]
            if layer in copper_types:
                if accumulate is not None:
                    board_thickness += accumulate
                    accumulate = 0.0
                else:
                    accumulate = 0.0
                    continue
            if accumulate is not None:
                accumulate += thickness

        coppers = self._copperLayers()
        if self.stackup:
            for _, name in coppers:
                if unquote(name) not in self._stackup_map:
                    self._log('stackup info ignored because copper layer {} is not found', name, level='warning')
                    self.stackup = []
                    self._stackup_map = {}
                    break

        if self.stackup:
            if board_thickness:
                self.board_thickness = board_thickness
        elif len(coppers) == 1:
            name = coppers[0][1]
            self._stackup_map[name] = [name, 0, self.copper_thickness]
        else:
            step = (self.board_thickness + self.copper_thickness) / max(1, (len(coppers) - 1))
            offset = self.board_thickness
            for _, name in coppers:
                self._stackup_map[name] = [name, offset, self.copper_thickness]
                offset -= step

        current = 1000.0
        for _, name in reversed(coppers):
            _, offset, thickness = self._stackup_map[name]
            if offset > current:
                self._dielectric_layers.append([current, offset - current])
            current = offset + thickness

    def layerOffsets(self, thickness=None):
        coppers = self._copperLayers()
        offsets = dict()
        if not thickness or thickness == self.board_thickness:
            for _, name in coppers:
                offsets[name] = self._stackup_map[name][1]
            return offsets

        if len(coppers) == 1:
            offsets[coppers[0][1]] = 0
            return offsets
        step = (thickness + self.copper_thickness) / (len(coppers) - 1)
        offset = thickness
        for _, name in coppers:
            offsets[name] = offset
            offset -= step
        return offsets

    def setNetFilter(self, *nets):
        self._nets.clear()
        ndict = dict()
        nset = set()
        for n in getattr(self.pcb, 'net', []):
            ndict[n[1]] = n[0]
            nset.add(n[0])

        for n in nets:
            try:
                self._nets.add(ndict[str(n)])
                continue
            except Exception:
                pass
            try:
                if int(n) in nset:
                    self._nets.add(int(n))
                    continue
            except Exception:
                pass
            logger.error('net {} not found'.format(n))

    def getNet(self, p):
        n = getattr(p, 'net', None)
        return n if not isinstance(n, list) else n[0]

    def filterNets(self, p):
        # Allow all elements if filter is empty
        if not self._nets:
            return False
        
        try:
            # Check element net association
            net = self.getNet(p)
            # If no explicit net parameter is defined, pass generic items (Edge.Cuts, Outlines)
            if net is None or net == '':
                return False
                
            return net not in self._nets
        except Exception:
            return False

    def filterLayer(self, p):
        layers = []
        l = getattr(p, 'layers', [])
        if unquote(l) == 'F&B.Cu':
            layers.append('F.Cu')
            layers.append('B.Cu')
        else:
            layers = [unquote(s) for s in l]
        if hasattr(p, 'layer'):
            layers.append(unquote(p.layer))
        if not layers:
            self._log('no layers specified', level='warning')
            return True
        if self.layer not in layers and self.layer_match not in layers and '*' not in layers:
            self._log('skip layer {}, {}, {}', self.layer, self.layer_match, layers, level='trace')
            return True

    def netName(self, p):
        try:
            return unquote(self.net_names[self.getNet(p)])
        except Exception:
            return 'net?'

    def _log(self, msg, *arg, **kargs):
        level = 'info'
        if kargs and 'level' in kargs:
            level = kargs['level']
        if logger.isEnabledFor(level):
            getattr(logger, level)('{}{}'.format(self.prefix, msg.format(*arg)))

    def _pushLog(self, msg=None, *arg, **kargs):
        if msg:
            self._log(msg, *arg, **kargs)
        if 'prefix' in kargs:
            prefix = kargs['prefix']
            if prefix is not None:
                self.prefix = prefix
        self.prefix += self.indent

    def _popLog(self, msg=None, *arg, **kargs):
        self.prefix = self.prefix[:-len(self.indent)]
        if msg:
            self._log(msg, *arg, **kargs)

    def _makeLabel(self, obj, label):
        if self.layer:
            obj.Label = '{}#{}'.format(obj.Name, self.layer)
        if label is not None:
            obj.Label += '#{}'.format(label)

    def _makeObject(self, otype, name, label=None, links=None, shape=None):
        doc = getActiveDoc()
        obj = addObject(doc, otype, name)
        self._makeLabel(obj, label)
        if links:
            setObjectLinks(obj, links, shape)
            for s in shape if isinstance(shape, (list, tuple)) else (shape,):
                if hasattr(s, 'ViewObject'):
                    s.ViewObject.Visibility = False
            if hasattr(obj, 'recompute'):
                recomputeObj(obj)
        return obj

    def _makeSketch(self, objs, name, label=None):
        if self.sketch_use_draft:
            import Draft
            getActiveDoc()
            nobj = Draft.makeSketch(objs, name=name, autoconstraints=True,
                delete=True, radiusPrecision=self.sketch_radius_precision)
            self._makeLabel(nobj, label)
            return nobj

        from Sketcher import Constraint
        StartPoint = 1
        EndPoint = 2
        doc = getActiveDoc()
        nobj = addObject(doc, "Sketcher::SketchObject", '{}_sketch'.format(name))
        self._makeLabel(nobj, label)
        nobj.ViewObject.Autoconstraints = False

        radiuses = {}
        constraints = []

        def addRadiusConstraint(edge):
            try:
                if self.sketch_radius_precision < 0:
                    return
                if self.sketch_radius_precision == 0:
                    constraints.append(Constraint('Radius', nobj.GeometryCount - 1, edge.Curve.Radius))
                    return
                r = round(edge.Curve.Radius, self.sketch_radius_precision)
                constraints.append(Constraint('Equal', radiuses[r], nobj.GeometryCount - 1))
            except KeyError:
                radiuses[r] = nobj.GeometryCount - 1
                constraints.append(Constraint('Radius', nobj.GeometryCount - 1, r))
            except AttributeError:
                pass

        for obj in objs if isinstance(objs, (list, tuple)) else (obj,):
            shape = obj if isinstance(obj, Part.Shape) else obj.Shape
            norm = DraftGeomUtils.getNormal(shape)
            if not self.sketch_constraint:
                for wire in shape.Wires:
                    for edge in wire.OrderedEdges:
                        nobj.addGeometry(DraftGeomUtils.orientEdge(edge, norm, make_arc=True))
                continue

            for wire in shape.Wires:
                last_count = nobj.GeometryCount
                edges = wire.OrderedEdges
                for edge in edges:
                    nobj.addGeometry(DraftGeomUtils.orientEdge(edge, norm, make_arc=True))
                    addRadiusConstraint(edge)

                for i, g in enumerate(nobj.Geometry[last_count:]):
                    if edges[i].Closed:
                        continue
                    seg = last_count + i
                    if self.sketch_align_constraint:
                        if DraftGeomUtils.isAligned(g, "x"):
                            constraints.append(Constraint("Vertical", seg))
                        elif DraftGeomUtils.isAligned(g, "y"):
                            constraints.append(Constraint("Horizontal", seg))

                    if seg == nobj.GeometryCount - 1:
                        if not wire.isClosed():
                            break
                        seg2 = last_count
                    else:
                        seg2 = seg + 1

                    g2 = nobj.Geometry[seg2]
                    end1 = g.value(g.LastParameter)
                    start2 = g2.value(g2.FirstParameter)
                    if DraftVecUtils.equals(end1, start2):
                        constraints.append(Constraint("Coincident", seg, EndPoint, seg2, StartPoint))
                        continue
                    end2 = g2.value(g2.LastParameter)
                    start1 = g.value(g.FirstParameter)
                    if DraftVecUtils.equals(end2, start1):
                        constraints.append(Constraint("Coincident", seg, StartPoint, seg2, EndPoint))
                    elif DraftVecUtils.equals(start1, start2):
                        constraints.append(Constraint("Coincident", seg, StartPoint, seg2, StartPoint))
                    elif DraftVecUtils.equals(end1, end2):
                        constraints.append(Constraint("Coincident", seg, EndPoint, seg2, EndPoint))

            if obj.isDerivedFrom("Part::Feature"):
                objs_to_remove = [obj]
                while objs_to_remove:
                    o = objs_to_remove[0]
                    objs_to_remove = objs_to_remove[1:] + o.OutList
                    doc.removeObject(o.Name)

        nobj.addConstraint(constraints)
        recomputeObj(nobj)
        return nobj

    def _makeCompound(self, obj, name, label=None, fit_arcs=False, fuse=False, add_feature=False, force=False):
        obj = unpack(obj)
        if not isinstance(obj, (list, tuple)):
            if not force and (not fuse or obj.TypeId == 'Path::FeatureArea'):
                return obj
            obj = [obj]
        if fuse:
            return self._makeArea(obj, name, label=label, fit_arcs=fit_arcs)
        if add_feature or self.add_feature:
            return self._makeObject('Part::Compound', '{}_combo'.format(name), label, 'Links', obj)
        return Part.makeCompound(obj)

    def _makeArea(self, obj, name, offset=0, op=0, fill=None, label=None, force=False, fit_arcs=False, reorient=False, outline=False):
        fill = 1 if fill else (2 if fill is None else 0)
        if not isinstance(obj, (list, tuple)):
            obj = (obj,)
        shape = obj[0] if isinstance(obj[0], Part.Shape) else Part.getShape(obj[0])
        workplane = self.getWorkPlane(shape)

        if self.add_feature and name:
            if not force and obj[0].TypeId == 'Path::FeatureArea' and (obj[0].Operation == op or len(obj[0].Sources) == 1) and obj[0].Fill == fill:
                ret = obj[0]
                if len(obj) > 1:
                    ret.Sources = list(ret.Sources) + list(obj[1:])
            else:
                ret = self._makeObject('Path::FeatureArea', '{}_area'.format(name), label)
                ret.Accuracy = self.arc_fit_accuracy
                ret.Sources = obj
                ret.Operation = op
                ret.Fill = fill
                ret.Offset = offset
                ret.Coplanar = 0
                ret.WorkPlane = workplane
                ret.FitArcs = fit_arcs
                ret.Reorient = reorient
                ret.Outline = outline
                for o in obj:
                    if hasattr(o, 'ViewObject'):
                        o.ViewObject.Visibility = False
            recomputeObj(ret)
        else:
            ret = Path.Area(Fill=fill, FitArcs=fit_arcs, Coplanar=0, Reorient=reorient, Accuracy=self.arc_fit_accuracy, Offset=offset, Outline=outline)
            ret.setPlane(workplane)
            for o in obj:
                ret.add(o, op=op)
            ret = ret.getShape()
        return ret

    def getWorkPlane(self, shape):
        z = shape.Vertex1.Point.z
        workplane = self.workplane.get(z, None)
        if not workplane:
            workplane = self.workplane[z] = Part.makeCircle(1, Vector(0, 0, z))
        return workplane

    def _makeWires(self, obj, name, offset=0, fill=False, label=None, fit_arcs=False, outline=False):
        if self.add_feature and name:
            if self.make_sketch:
                obj = self._makeSketch(obj, name, label)
            elif isinstance(obj, Part.Shape):
                obj = self._makeObject('Part::Feature', '{}_wire'.format(name), label, 'Shape', obj)
            elif isinstance(obj, (list, tuple)):
                objs, comp = [], []
                for o in obj:
                    if isinstance(o, Part.Shape):
                        comp.append(o)
                    else:
                        objs.append(o)
                if comp:
                    comp_shape = Part.makeCompound(comp)
                    objs.append(self._makeObject('Part::Feature', '{}_wire'.format(name), label, 'Shape', comp_shape))
                obj = objs

        if outline or fill or offset:
            return self._makeArea(obj, name, offset=offset, fill=fill, fit_arcs=fit_arcs, label=label, outline=outline)
        return self._makeCompound(obj, name, label=label)

    def _makeSolid(self, obj, name, height, label=None, fit_arcs=True):
        obj = self._makeCompound(obj, name, label=label, fuse=True, fit_arcs=fit_arcs)
        if not self.add_feature:
            return obj.extrude(Vector(0, 0, height))
        nobj = self._makeObject('Part::Extrusion', '{}_solid'.format(name), label)
        nobj.Base = obj
        nobj.Dir = Vector(0, 0, height)
        if hasattr(obj, 'ViewObject'):
            obj.ViewObject.Visibility = False
        recomputeObj(nobj)
        return nobj

    def _makeFuse(self, objs, name, label=None, force=False):
        obj = unpack(objs)
        if not isinstance(obj, (list, tuple)):
            if not force:
                return obj
            obj = [obj]
        name = '{}_fuse'.format(name)
        if self.add_feature:
            self._log('making fuse {}...', name)
            obj = self._makeObject('Part::MultiFuse', name, label, 'Shapes', obj)
            obj.Refine = self.refine
            self._log('fuse done')
            return obj
        solids = []
        for o in obj:
            solids += o.Solids
        if solids:
            self._log('making fuse {}...', name)
            obj = solids[0].multiFuse(solids[1:])
            if self.refine:
                try:
                    obj = obj.removeSplitter()
                except: pass
            self._log('fuse done')
            return obj

    def _makeGeneralFuse(self, objs, name, label=None):
        """
        Global optimized generalFuse boolean intersect/partition algorithm.
        This provides a mathematically robust, non-overlapping solid for FEM meshing
        where internal volumes and touching faces are safely resolved together.
        """
        if not objs:
            return None
        
        flat_objs = []
        for o in objs:
            if isinstance(o, (list, tuple)):
                flat_objs.extend(o)
            else:
                flat_objs.append(o)
        
        shapes = [o.Shape if hasattr(o, "Shape") else o for o in flat_objs]
        
        if len(shapes) > 1:
            fused_shape, _ = shapes[0].generalFuse(shapes[1:])
        else:
            fused_shape = shapes[0]

        if self.add_feature:
            doc = FreeCAD.ActiveDocument
            fused_obj = addObject(doc, "Part::Feature", name)
            self._makeLabel(fused_obj, label)
            fused_obj.Shape = fused_shape

            for o in flat_objs:
                if hasattr(o, "ViewObject") and o != fused_obj:
                    o.ViewObject.Visibility = False
            return fused_obj
        else:
            return fused_shape

    def _makeCut(self, base, tool, name, label=None):
        base = self._makeFuse(base, name, label=label)
        tool = self._makeFuse(tool, 'drill', label=label)
        name = '{}_drilled'.format(name)
        self._log('making cut {}...', name)
        if self.add_feature:
            cut = self._makeObject('Part::Cut', name, label=label)
            cut.Base = base
            cut.Tool = tool
            cut.Refine = self.refine
            if hasattr(base, 'ViewObject'): base.ViewObject.Visibility = False
            if hasattr(tool, 'ViewObject'): tool.ViewObject.Visibility = False
            recomputeObj(cut)
            if hasattr(base, 'ViewObject') and hasattr(cut, 'ViewObject'):
                cut.ViewObject.ShapeColor = base.ViewObject.ShapeColor
        else:
            cut = base.cut(tool)
            if self.refine:
                cut = cut.removeSplitter()
        self._log('cut done')
        return cut

    def _place(self, obj, pos, angle=None):
        if not hasattr(obj, 'isDerivedFrom') or not obj.isDerivedFrom('App::DocumentObject'):
            if angle:
                obj.rotate(Vector(), Vector(0, 0, 1), angle)
            obj.translate(pos)
        else:
            r = Rotation(Vector(0, 0, 1), angle) if angle else Rotation()
            obj.Placement = Placement(pos, r)
            obj.purgeTouched()

    def _makeEdgeCuts(self, sexp, ctx, wires, non_closed, at=None, layers=None):
        if not layers:
            layers = [44]
        for l in layers:
            try:
                _, layer = self.findLayer(l)
            except Exception:
                continue
            self._makeShape(sexp, ctx, wires, non_closed, layer, at)

    def _makeShape(self, sexp, ctx, wires, non_closed=None, layer=None, at=None):
        edges = []
        angle = None
        if at:
            at, angle = getAt(at)

        for tp in ('line', 'arc', 'circle', 'curve', 'poly', 'rect'):
            name = ctx + '_' + tp
            primitives = getattr(sexp, name, None)
            if not primitives:
                continue
            primitives = SexpList(primitives)
            self._log('making {} {}s', len(primitives), tp)
            make_shape = globals()['make_gr_{}'.format(tp)]
            for l in primitives:
                if not layer:
                    if self.filterNets(l) or self.filterLayer(l):
                        continue
                elif getattr(l, 'layer', None) != layer:
                    continue
                shape = make_shape(l)
                if angle:
                    shape.rotate(Vector(), Vector(0, 0, 1), angle)
                if at:
                    shape.translate(at)
                width = getLineWidth(l, 1e-7)
                edges += [[width, e] for e in shape.Edges]

        for info in edges:
            w, e = info
            if w > 1e-7:
                e.fixTolerance(w)
            info += [e.firstVertex().Point, e.lastVertex().Point]

        while edges:
            w, e, pstart, pend = edges.pop(-1)
            wstart = wend = w
            elist = [(w, e)]
            closed = pstart.distanceToPoint(pend) <= (wstart + w) / 2
            i = 0
            while not closed and i < len(edges):
                w, e, ps, pe = edges[i]
                if pstart.distanceToPoint(ps) <= (wstart + w) / 2:
                    e.reverse()
                    pstart = pe
                    wstart = w
                    elist.insert(0, (w, e))
                elif pstart.distanceToPoint(pe) <= (wstart + w) / 2:
                    pstart = ps
                    wstart = w
                    elist.insert(0, (w, e))
                elif pend.distanceToPoint(ps) <= (wend + w) / 2:
                    e.reverse()
                    pend = pe
                    wend = w
                    elist.append((w, e))
                elif pend.distanceToPoint(pe) <= (wend + w) / 2:
                    pend = ps
                    wend = w
                    elist.append((w, e))
                else:
                    i += 1
                    continue
                edges.pop(i)
                i = 0
                if pstart.distanceToPoint(pend) <= (wstart + wend) / 2:
                    closed = True
                    break

            wire = None
            try:
                wire = Part.Wire([disableTopoNaming(o[1]) for o in elist])
            except Exception:
                pass

            if closed and (not wire or not wire.isClosed()):
                logger.warning('wire not closed')
                closed = False

            if wire and closed:
                wires.append(wire)
            elif non_closed is not None:
                for w, e in elist:
                    if w > 5e-7:
                        non_closed[w].append(e)
            else:
                for w, e in elist:
                    if w > 5e-7:
                        wires.append(self._makeWires(e, name=None, offset=w * 0.5))

    def intersectBoard(self, objs, name, fit_arcs=True):
        if not objs:
            return objs
        if self.add_feature and self.board_uid != getActiveDoc().Uid:
            self.board_face = None
        if not self.board_face:
            self.board_face = self.makeBoard(shape_type='face', holes=False, single_layer=True)
            if self.add_feature and hasattr(self.board_face, 'ViewObject'):
                self.board_face.ViewObject.Visibility = False
                self.board_uid = self.board_face.Document.Uid
        objs = (self._makeCompound(objs, name, label='castellated'), self.board_face)
        return self._makeArea(objs, name, op=2, label='castellated', fit_arcs=fit_arcs)

    def makeBoard(self, shape_type='solid', thickness=None, fit_arcs=True, holes=True, minHoleSize=0, ovalHole=True, prefix='', single_layer=False):
        non_closed = defaultdict(list)
        wires = []
        self._pushLog('making board...', prefix=prefix)
        self._makeEdgeCuts(self.pcb, 'gr', wires, non_closed)

        self._pushLog('checking footprints...', prefix=prefix)
        if self.module:
            self._makeEdgeCuts(self.module, 'fp', wires, non_closed)
            self._makeEdgeCuts(self.module, 'fp', wires, non_closed, layers=(46, 47))
        else:
            for m in self.pcb.module:
                self._makeEdgeCuts(m, 'fp', wires, non_closed, getattr(m, 'at', None))
        self._popLog()

        if not wires and not non_closed:
            self._popLog('no board edges found')
            return

        def _addHoles(objs):
            h = self._cutHoles(None, holes, None, minSize=minHoleSize, oval=ovalHole)
            if h:
                if isinstance(h, (tuple, list)):
                    objs += h
                elif holes:
                    objs.append(h)
            return objs

        def _wire():
            objs = []
            if wires:
                objs.append(self._makeWires(wires, 'board'))
            for width, edges in non_closed.items():
                objs.append(self._makeWires(edges, 'board', label=str(width), offset=width * 0.5))
            return self._makeCompound(_addHoles(objs), 'board')

        def _face():
            if not wires:
                raise RuntimeError('no closed wire')
            areas = [Part.Face(w).Area for w in wires]
            outer = wires.pop(areas.index(max(areas)))
            objs = [self._makeWires(outer, 'board', label='outline')]
            if wires:
                objs.append(self._makeWires(wires, 'board', label='inner'))
            for width, elist in non_closed.items():
                wire = self._makeWires(elist, 'board', label=str(width))
                objs.append(self._makeArea(wire, 'board', label=str(width), offset=width * 0.5))
            return self._makeArea(_addHoles(objs), 'board', op=1, fill=True, fit_arcs=fit_arcs)

        base = []
        def _solid():
            base.append(_face())
            return self._makeSolid(base[0], 'board', thickness, fit_arcs=fit_arcs)

        if shape_type == 'solid' and not thickness and self._dielectric_layers:
            layers = self._dielectric_layers
        else:
            if not thickness:
                thickness = self.board_thickness
            layers = [(self.copper_thickness, thickness)]

        try:
            layer_save = self.layer
            self.layer = None
            func = locals()['_{}'.format(shape_type)]
            thickness = layers[0][1]
            obj = func()
            self.setColor(obj, 'board')

            if len(layers) > 1 and not single_layer:
                objs = [obj]
                for offset, t in layers[1:]:
                    if abs(t - layers[0][1]) < 1e-7:
                        if self.add_feature:
                            obj = self._makeObject('Part::Feature', 'board_solid')
                            obj.Shape = objs[0].Shape
                        else:
                            obj = objs[0].copy()
                    else:
                        obj = self._makeSolid(base[0], 'board', t)
                    self._place(obj, Vector(0, 0, offset))
                    self.setColor(obj, 'board')
                    objs.append(obj)
                obj = self._makeCompound(objs, 'board')
                self.setColor(obj, 'board')
        finally:
            if layer_save:
                self.setLayer(layer_save)

        self._popLog('board done')
        fitView()
        return obj

    def makeHoles(self, shape_type='wire', minSize=0, maxSize=0, oval=False, prefix='', offset=0.0, npth=0, skip_via=False, board_thickness=None, extra_thickness=0.0, castellated=False):
        self._pushLog('making holes...', prefix=prefix)
        holes = defaultdict(list)
        ovals = defaultdict(list)
        width = 0

        def _wire(obj, name, fill=False):
            return self._makeWires(obj, name, fill=fill, label=str(width))
        def _face(obj, name):
            return _wire(obj, name, True)
        def _solid(obj, name):
            return self._makeWires(obj, name, fill=True, label=str(width), fit_arcs=True)

        try:
            func = locals()['_{}'.format(shape_type)]
        except KeyError:
            raise ValueError('invalid shape type: {}'.format(shape_type))

        oval_count = 0
        count = 0
        skip_count = 0
        if not offset:
            offset = self.hole_size_offset

        thickness = board_thickness if board_thickness else self.board_thickness
        layer_offsets = self.layerOffsets(thickness)
        z_offset = min(layer_offsets.values()) if layer_offsets else 0

        for m in self.pcb.module:
            m_at, m_angle = getAt(m)
            for p in m.pad:
                if 'drill' not in p:
                    continue
                if self.filterNets(p):
                    skip_count += 1
                    continue
                if p[1] == 'np_thru_hole':
                    if npth < 0:
                        skip_count += 1
                        continue
                    ofs = abs(offset)
                else:
                    if npth > 0:
                        skip_count += 1
                        continue
                    ofs = -abs(offset)
                if p.drill.oval:
                    if not oval:
                        continue
                    size = Vector(p.drill[0], p.drill[1])
                    w = make_oval(size + Vector(ofs, ofs))
                    ovals[min(size.x, size.y)].append(w)
                    oval_count += 1
                elif 0 in p.drill and p.drill[0] >= minSize and (not maxSize or p.drill[0] <= maxSize):
                    w = make_circle(Vector(p.drill[0] + ofs))
                    holes[p.drill[0]].append(w)
                    count += 1
                else:
                    skip_count += 1
                    continue
                at, angle = getAt(p)
                angle -= m_angle
                if not isZero(angle):
                    w.rotate(Vector(), Vector(0, 0, 1), angle)
                w.translate(at)
                if m_angle:
                    w.rotate(Vector(), Vector(0, 0, 1), m_angle)
                m_at.z = z_offset
                w.translate(m_at)

        self._log('pad holes: {}, skipped: {}', count + skip_count, skip_count)
        if oval:
            self._log('oval holes: {}', oval_count)

        blind_holes = defaultdict(list)
        if npth <= 0:
            via_skip = 0
            if skip_via or self.via_bound < 0:
                via_skip = len(self.pcb.via)
            else:
                ofs = -abs(offset)
                for v in self.pcb.via:
                    if self.filterNets(v):
                        via_skip += 1
                        continue
                    if v.drill >= minSize and (not maxSize or v.drill <= maxSize):
                        # Graceful handling for missing layers within Via definition
                        z_offsets = [layer_offsets[unquote(n)] for n in v.layers if unquote(n) in layer_offsets]
                        if not z_offsets:
                            z_offsets = [0, thickness]
                        pos = makeVect(v.at)
                        pos.z = min(z_offsets)
                        dist = max(z_offsets) - pos.z
                        s = v.drill + ofs
                        w = make_rect(Vector(s, s)) if self.via_bound else make_circle(Vector(s))
                        w.translate(pos)
                        if dist < thickness - 0.001:
                            blind_holes[(pos.z, dist)].append(w)
                        else:
                            holes[v.drill].append(w)
                    else:
                        via_skip += 1
            skip_count += via_skip
            self._log('via holes: {}, skipped: {}', len(self.pcb.via), via_skip)

        objs = []
        if blind_holes or holes or ovals:
            if self.merge_holes:
                for o in ovals.values(): objs += o
                for o in holes.values(): objs += o
                if objs: objs = func(objs, "holes")
            else:
                for r in ((ovals, 'oval'), (holes, 'hole')):
                    if not r[0]: continue
                    for (width, rs) in r[0].items():
                        objs.append(func(rs, r[1]))

            label = 'npth' if npth > 0 else ('th' if npth < 0 else None)
            if castellated:
                objs = self.intersectBoard(objs, 'holes', fit_arcs=True)

            if shape_type != 'solid':
                if not objs:
                    self._popLog('no holes')
                    return
                objs = self._makeCompound(objs, 'holes', label=label)
            else:
                thickness = board_thickness if board_thickness else self.board_thickness
                thickness += extra_thickness
                pos = -0.01
                if npth >= -1 and 'F.Cu' in self._stackup_map:
                    thickness += self._stackup_map['F.Cu'][2]
                if objs:
                    objs = self._makeSolid(objs, 'holes', thickness, label=label)
                if blind_holes:
                    if not isinstance(objs, (tuple, list)):
                        objs = [objs] if objs else []
                    for (_, d), o in blind_holes.items():
                        if npth >= -1: d += extra_thickness
                        objs.append(self._makeSolid(func(o, 'blind'), 'blind', d, label=label))
                    objs = self._makeCompound(objs, 'holes', label=label)
                self._place(objs, FreeCAD.Vector(0, 0, pos))

        self._popLog('holes done')
        return objs

    def _cutHoles(self, objs, holes, name, label=None, fit_arcs=False, minSize=0, maxSize=0, oval=True, npth=0, offset=0.0):
        if not holes:
            return objs
        if not hasattr(holes, 'TypeId'):
            hit = False
            if self.holes_cache is not None:
                key = '{}.{}.{}.{}.{}.{}.{}'.format(self.add_feature, minSize, maxSize, oval, npth, offset, self.via_bound)
                doc = getActiveDoc()
                if self.add_feature and self.active_doc_uuid != doc.Uid:
                    self.holes_cache.clear()
                    self.active_doc_uuid = doc.Uid
                try:
                    holes = self.holes_cache[key]
                    hit = True
                except KeyError:
                    pass
            if not hit:
                self._pushLog()
                holes = self.makeHoles(shape_type='wire', prefix=None, npth=npth, minSize=minSize, maxSize=maxSize, oval=oval, offset=offset)
                self._popLog()
                if isinstance(self.holes_cache, dict):
                    self.holes_cache[key] = holes

        if not holes: return objs
        if not objs: return holes

        objs = (self._makeCompound(objs, name, label=label), holes)
        return self._makeArea(objs, name, op=1, label=label, fit_arcs=fit_arcs)

    def _makeCustomPad(self, params):
        wires = []
        anchor = getattr(getattr(params, 'options', None), 'anchor', None)
        if anchor in ('rect', 'circle'):
            w = globals()[f'make_{anchor}'](Vector(*params.size))
            wires.append(w)
        for key in params.primitives:
            primitives = SexpList(getattr(params.primitives, key))
            for param in primitives:
                wire, width = makePrimitve(key, param)
                if not width:
                    if isinstance(wire, Part.Edge): wire = Part.Wire(wire)
                    wires.append(wire)
                else:
                    wire = self._makeWires(wire, name=None, offset=width * 0.5)
                    wires += wire.Wires
        if not wires: return
        return wires[0] if len(wires) == 1 else Part.makeCompound(wires)

    def getTrackPoints(self):
        points = set()
        for tp, ss in (('segment', self.pcb.segment), ('arc', getattr(self.pcb, 'arc', []))):
            for s in ss:
                if self.filterNets(s): continue
                if unquote(s.layer) == self.layer:
                    points.add((s.start[0], s.start[1]))
                    points.add((s.end[0], s.end[1]))
        return points

    def makePads(self, shape_type='face', thickness=0.05, holes=False, fit_arcs=True, prefix=''):
        self._pushLog('making pads...', prefix=prefix)

        def _wire(obj, name, label=None, fill=False):
            return self._makeWires(obj, name, fill=fill, label=label, offset=self.pad_inflate)
        def _face(obj, name, label=None):
            objs = _wire(obj, name, label, True)
            if not cut_wires and not cut_non_closed: return objs
            if not isinstance(objs, list): objs = [objs]
            inner_label = label + '_inner' if label else 'inner'
            if cut_wires: objs.append(self._makeWires(cut_wires, name, label=inner_label))
            for width, elist in cut_non_closed.items():
                l = '{}_{}'.format(inner_label, width)
                wire = self._makeWires(elist, name, label=l)
                objs.append(self._makeArea(wire, name, label=l, offset=width * 0.5))
            return self._makeArea(objs, name, op=1, fill=True)
        _solid = _face

        try:
            func = locals()['_{}'.format(shape_type)]
        except KeyError:
            raise ValueError('invalid shape type: {}'.format(shape_type))

        objs = []
        track_points = None

        def filter_unconnected(v, at):
            if 'remove_unused_layers' in v:
                for s in getattr(v, 'zone_layer_connections', []):
                    try:
                        if self.layer_type == self.findLayer(s)[0]: return
                    except Exception: pass
                nonlocal track_points
                if track_points is None: track_points = self.getTrackPoints()
                if at not in track_points: return True

        for i, m in enumerate(self.pcb.module):
            ref = ''
            for t in m.fp_text:
                if t[0] == 'reference': ref = t[1]; break
            m_at, m_angle = getAt(m)
            pads = []
            cut_wires = []
            cut_non_closed = defaultdict(list)
            self._makeEdgeCuts(m, 'fp', cut_wires, cut_non_closed)

            for j, p in enumerate(m.pad):
                if self.filterNets(p) or self.filterLayer(p): continue
                shape = p[2]
                if shape == 'custom':
                    w = self._makeCustomPad(p)
                else:
                    make_shape = globals()['make_{}'.format(shape)]
                    w = make_shape(Vector(*p.size), p)
                if not w: continue
                if 'drill' in p and 'offset' in p.drill:
                    w.translate(makeVect(p.drill.offset))
                at, angle = getAt(p)
                angle -= m_angle
                if not isZero(angle): w.rotate(Vector(), Vector(0, 0, 1), angle)
                w.translate(at)
                if not self.merge_pads:
                    pads.append(func(w, 'pad', f'{i}#{j}#{p[0]}#{ref}#{self.netName(p)}#{shape}'))
                else:
                    pads.append(w)

            self._makeShape(m, 'fp', pads)
            if not pads: continue
            obj = self._makeCompound(pads, 'pads', '{}#{}'.format(i, ref)) if not self.merge_pads else func(pads, 'pads', '{}#{}'.format(i, ref))
            self._place(obj, m_at, m_angle)
            objs.append(obj)

        vias = []
        if self.via_bound >= 0:
            for idx, v in enumerate(self.pcb.via):
                layers = [self.findLayer(s)[0] for s in v.layers]
                if self.layer_type < min(layers) or self.layer_type > max(layers) or self.filterNets(v): continue
                if filter_unconnected(v, (v.at[0], v.at[1])): continue
                w = make_rect(Vector(v.size * self.via_bound, v.size * self.via_bound)) if self.via_bound else make_circle(Vector(v.size))
                w.translate(makeVect(v.at))
                if not self.merge_vias:
                    vias.append(func(w, 'via', '{}#{}'.format(idx, v.size)))
                else:
                    vias.append(w)

        if vias:
            objs.append(func(vias, 'vias') if self.merge_vias else self._makeCompound(vias, 'vias'))

        if objs:
            if self.castellated: objs = self.intersectBoard(objs, 'pads', fit_arcs=fit_arcs)
            objs = self._cutHoles(objs, holes, 'pads', fit_arcs=fit_arcs)
            objs = self._makeSolid(objs, 'pads', thickness, fit_arcs=fit_arcs) if shape_type == 'solid' else self._makeCompound(objs, 'pads', fuse=True, fit_arcs=fit_arcs)
            self.setColor(objs, 'pad')

        self._popLog('pads done')
        fitView()
        return objs

    def setColor(self, obj, otype):
        if not self.add_feature or not hasattr(obj, 'ViewObject'): return
        try:
            color = self.colors[otype][self.layer_type]
        except KeyError:
            color = self.colors[otype][0]
        if hasattr(obj.ViewObject, 'MapFaceColor'): obj.ViewObject.MapFaceColor = False
        obj.ViewObject.ShapeColor = color

    def makeTracks(self, shape_type='face', fit_arcs=True, thickness=0.05, holes=False, prefix=''):
        self._pushLog('making tracks...', prefix=prefix)
        width = 0

        def _line(edges, label, offset=0, fill=False):
            wires = findWires(edges)
            return self._makeWires(wires, 'track', offset=offset, fill=fill, label=label, fit_arcs=fit_arcs)
        def _wire(edges, label, fill=False):
            return _line(edges, label, width * 0.5, fill)
        def _face(edges, label):
            return _wire(edges, label, True)
        _solid = _face

        try:
            func = locals()['_{}'.format(shape_type)]
        except KeyError:
            raise ValueError('invalid shape type: {}'.format(shape_type))

        tracks = defaultdict(lambda: defaultdict(list))
        for tp, ss in (('segment', self.pcb.segment), ('arc', getattr(self.pcb, 'arc', []))):
            for s in ss:
                if self.filterNets(s): continue
                if unquote(s.layer) == self.layer:
                    name = '' if self.merge_tracks else self.netName(s)
                    tracks[name][s.width].append((tp, s))

        objs = []
        for (name, sss) in tracks.items():
            for (w_val, ss) in sss.items():
                width = w_val
                edges = []
                for tp, s in ss:
                    if tp == 'segment' and s.start != s.end:
                        edges.append(Part.makeLine(makeVect(s.start), makeVect(s.end)))
                    elif tp == 'arc':
                        if s.start != s.end:
                            edges.append(Part.ArcOfCircle(makeVect(s.end), makeVect(s.mid), makeVect(s.start)).toShape())
                        else:
                            start = makeVect(s.start)
                            middle = makeVect(s.mid)
                            edges.append(Part.makeCircle(start.distanceToPoint(middle), (middle - start) / 2))
                label = '{}'.format(width) if self.merge_tracks else '{}#{}'.format(width, name)
                objs.append(func(edges, label=label))

        if objs:
            if self.castellated: objs = self.intersectBoard(objs, 'tracks', fit_arcs=fit_arcs)
            objs = self._cutHoles(objs, holes, 'tracks', fit_arcs=fit_arcs)
            objs = self._makeSolid(objs, 'tracks', thickness, fit_arcs=fit_arcs) if shape_type == 'solid' else self._makeCompound(objs, 'tracks', fuse=True, fit_arcs=fit_arcs)
            self.setColor(objs, 'track')

        self._popLog('tracks done')
        fitView()
        return objs

    def _makePolygons(self, fields, name, poly_holes, shape_type='face', thickness=0.05, prefix=''):
        if not fields: return []
        self._pushLog(f'making {len(fields)} polygons...', prefix=prefix)

        def _wire(obj, fill=False):
            offset = self.zone_inflate + thickness * 0.5
            if not poly_holes or (self.add_feature and self.make_sketch and self.zone_merge_holes):
                obj = [obj] + poly_holes
            elif poly_holes:
                obj = (self._makeWires(obj, f'{name}_outline'), self._makeWires(poly_holes, f'{name}_hole'))
                return self._makeArea(obj, name, offset=offset, op=1, fill=fill)
            return self._makeWires(obj, name, fill=fill, offset=offset)
        def _face(obj): return _wire(obj, True)
        _solid = _face

        try:
            func = locals()['_{}'.format(shape_type)]
        except KeyError:
            raise ValueError('invalid shape type: {}'.format(shape_type))

        objs = []
        for p in fields:
            if (hasattr(p, 'layer') or hasattr(p, 'layers')) and self.filterLayer(p): continue
            poly_holes = []
            table = {}
            pts = SexpList(p.pts.xy)
            pts._append(p.pts.xy._get(0))

            for i in range(len(pts) - 1):
                table[str((pts[i], pts[i+1]))] = i

            def build(start, end):
                results = []
                while start < end:
                    key = str((pts[start+1], pts[start]))
                    try:
                        idx = table[key]
                        del table[key]
                    except KeyError:
                        results.append(Part.makeLine(makeVect(pts[start]), makeVect(pts[start+1])))
                        start += 1
                        continue
                    h = build(start + 1, idx)
                    if h: poly_holes.append(Part.Wire(h))
                    start = idx + 1
                return results

            edges = build(0, len(pts) - 1)
            objs.append(func(Part.Wire(edges)))
        self._popLog('polygons done')
        return objs

    def makePolys(self, shape_type='face', thickness=0.05, fit_arcs=True, holes=False, prefix=''):
        poly_holes = []
        objs = self._makePolygons(getattr(self.pcb, 'gr_poly', None), 'poly', poly_holes, shape_type, thickness, prefix)
        if not objs: return
        objs = self._cutHoles(objs, holes, 'polys')
        objs = self._makeSolid(objs, 'polys', thickness, fit_arcs=fit_arcs) if shape_type == 'solid' else self._makeCompound(objs, 'polys', fuse=holes, fit_arcs=fit_arcs)
        self.setColor(objs, 'zone')
        fitView()
        return objs

    def makeZones(self, shape_type='face', thickness=0.05, fit_arcs=True, holes=False, prefix=''):
        self._pushLog('making zones...', prefix=prefix)
        zone_holes = []
        objs = []
        for z in getattr(self.pcb, 'zone', []):
            if self.filterNets(z) or self.filterLayer(z): continue
            objs += self._makePolygons(z.filled_polygon, 'zone', zone_holes, shape_type, thickness, prefix)
        if objs:
            if self.castellated: objs = self.intersectBoard(objs, 'zones', fit_arcs=fit_arcs)
            objs = self._cutHoles(objs, holes, 'zones')
            objs = self._makeSolid(objs, 'zones', thickness, fit_arcs=fit_arcs) if shape_type == 'solid' else self._makeCompound(objs, 'zones', fuse=holes, fit_arcs=fit_arcs)
            self.setColor(objs, 'zone')
        self._popLog('zones done')
        fitView()
        return objs

    def isBottomLayer(self):
        copper_types = [x[0] for x in self._copperLayers()]
        return self.layer_type == max(copper_types) if copper_types else False

    def makeCopper(self, shape_type='face', thickness=0.05, fit_arcs=True, holes=False, z=0, prefix='', fuse=False, layer_idx=0, total_layers=1):
        self._pushLog('making copper layer {}...', self.layer, prefix=prefix)
        holes = self._cutHoles(None, holes, None)
        objs = []
        solid = shape_type == 'solid'
        sub_fit_arcs = fit_arcs if solid else False
        st = 'face' if (solid and fuse) else shape_type

        features = [('Pads', thickness), ('Tracks', 0.5 * thickness), ('Zones', 0), ('Polys', thickness)]
        total_features = len(features)

        for f_idx, (name, offset) in enumerate(features):
            current_step = (layer_idx * total_features) + f_idx
            total_steps = total_layers * total_features
            percent = int((current_step / total_steps) * 100)
            self._log('Progress: {}% - Layer {} (Generating {}...)', percent, self.layer, name)

            obj = getattr(self, 'make{}'.format(name))(fit_arcs=sub_fit_arcs, holes=holes, shape_type=st, prefix=None, thickness=thickness)
            if not obj: continue
            if solid and not fuse:
                copper_types = [x[0] for x in self._copperLayers()]
                mid = sum(copper_types) / len(copper_types) if copper_types else 0
                ofs = thickness if self.layer_type < mid else -thickness
                self._place(obj, Vector(0, 0, ofs))
            objs.append(obj)

        if not objs: return
        if solid and not fuse:
            obj = self._makeCompound(objs, 'copper')
        else:
            obj = self._makeArea(objs, 'copper', fit_arcs=fit_arcs)
            self.setColor(obj, 'copper')
            if solid:
                obj = self._makeSolid(obj, 'copper', thickness)
                self.setColor(obj, 'copper')

        self._place(obj, Vector(0, 0, z))
        fitView()
        return obj

    def makeCoppers(self, shape_type='face', fit_arcs=True, prefix='', holes=False, board_thickness=None, thickness=None, fuse=False):
        self._pushLog('making all copper layers...', prefix=prefix)
        layer_save = self.layer
        objs, layers, thicknesses, offsets = [], [], [], []

        if not board_thickness or not thickness:
            for layer, name in self._copperLayers():
                layers.append(layer)
                _, offset, t = self._stackup_map[name]
                offsets.append(offset)
                thicknesses.append(t)
        else:
            for layer, name in self._copperLayers():
                layers.append(layer)
                if not hasattr(thickness, 'get'):
                    thicknesses.append(float(thickness))
                else:
                    for key in (layer, str(layer), name, None, ''):
                        try:
                            thicknesses.append(float(thickness.get(key)))
                            break
                        except Exception: pass
            z_step = 0 if len(layers) == 1 else (board_thickness + thicknesses[-1]) / (len(layers) - 1)
            offsets = [board_thickness - i * z_step for i, _ in enumerate(layers)]

        thickness = max(thicknesses) if thicknesses else self.copper_thickness
        if not layers: raise ValueError('no copper layer found')

        if not holes:
            hole_shapes = None
        elif fuse:
            hole_shapes = self._cutHoles(None, holes, None, npth=1)
        else:
            hole_shapes = self._cutHoles(None, holes, None)

        try:
            total_layers = len(layers)
            for idx, (layer, t, z) in enumerate(zip(layers, thicknesses, offsets)):
                self.setLayer(layer)
                copper = self.makeCopper(shape_type, t, fit_arcs=fit_arcs, holes=hole_shapes, z=z, prefix=None, fuse=fuse, layer_idx=idx, total_layers=total_layers)
                if copper: objs.append(copper)
        finally:
            if layer_save: self.setLayer(layer_save)

        if not objs: return

        if shape_type == 'solid' and fuse:
            hole_coppers = self.makeHoles(shape_type='solid', prefix=None, oval=True, npth=-2, board_thickness=board_thickness, extra_thickness=thickness, castellated=self.castellated)
            if hole_coppers:
                self.setColor(hole_coppers, 'copper')
                self._place(hole_coppers, FreeCAD.Vector(0, 0, thickness * 0.5))
                objs.append(hole_coppers)

            # Replacing recursive loops with generalFuse mathematically robust partition logic
            objs = self._makeGeneralFuse(objs, 'coppers')
            self.setColor(objs, 'copper')

            if holes:
                drills = self.makeHoles(shape_type='solid', prefix=None, board_thickness=board_thickness, extra_thickness=1.1 * thickness, oval=True, npth=-1, offset=thickness, skip_via=self.via_skip_hole)
                if drills:
                    self._place(drills, FreeCAD.Vector(0, 0, -0.05 * thickness))
                    objs = self._makeCut(objs, drills, 'coppers')
                    self.setColor(objs, 'copper')

        fitView()
        return objs

    def loadParts(self, z=0, combo=False, prefix=''):
        if not os.path.isdir(self.part_path): raise Exception('cannot find kicad package3d directory')
        self._pushLog('loading parts on layer {}...', self.layer, prefix=prefix)
        at_bottom = self.isBottomLayer()
        if z == 0:
            z = -0.1 if at_bottom else (self.pcb.general.thickness + 0.1)

        parts = [] if (self.add_feature or combo) else {}

        for (module_idx, m) in enumerate(self.pcb.module):
            if unquote(m.layer) != self.layer: continue
            ref = '?'
            for t in m.fp_text:
                if t[0] == 'reference': ref = t[1]; break
            m_at, m_angle = getAt(m)
            m_at += Vector(0, 0, z)
            objs = []
            for (model_idx, model) in enumerate(m.model):
                path = os.path.splitext(model[0])[0]
                for e in ('.stp', '.STP', '.step', '.STEP'):
                    filename = os.path.join(self.part_path, path + e)
                    mobj = loadModel(filename)
                    if not mobj: continue
                    at = product(Vector(*model.at.xyz), Vector(25.4, 25.4, 25.4))
                    rot = [-float(v) for v in reversed(model.rotate.xyz)]
                    pln = Placement(at, Rotation(*rot))
                    if not self.add_feature:
                        obj = mobj[0].copy() if combo else {'shape': mobj[0].copy(), 'color': mobj[1]}
                        if combo: obj.Placement = pln
                        else: obj['shape'].Placement = pln
                        objs.append(obj)
                    else:
                        obj = self._makeObject('Part::Feature', 'model', label='{}#{}#{}'.format(module_idx, model_idx, ref), links='Shape', shape=mobj[0])
                        obj.ViewObject.DiffuseColor = mobj[1]
                        obj.Placement = pln
                        objs.append(obj)
                    break
            if not objs: continue
            pln = Placement(m_at, Rotation(Vector(0, 0, 1), m_angle))
            if at_bottom: pln = pln.multiply(Placement(Vector(), Rotation(Vector(1, 0, 0), 180)))
            label = '{}#{}'.format(module_idx, ref)
            if self.add_feature or combo:
                obj = self._makeCompound(objs, 'part', label, force=True)
                obj.Placement = pln
                parts.append(obj)
            else:
                parts[label] = {'pos': pln, 'models': objs}

        if parts and not combo and self.add_feature:
            grp = self._makeObject('App::DocumentObjectGroup', 'parts')
            for o in parts: grp.addObject(o)
            parts = grp
        elif parts and combo:
            parts = self._makeCompound(parts, 'parts')

        fitView()
        return parts

    def loadAllParts(self, combo=False):
        layer = self.layer
        objs = []
        copper_layers = self._copperLayers()
        if copper_layers:
            try:
                self.setLayer(copper_layers[0][0])
                objs.append(self.loadParts(combo=combo))
            except Exception as e: self._log('{}', e, level='error')
            if len(copper_layers) > 1:
                try:
                    self.setLayer(copper_layers[-1][0])
                    objs.append(self.loadParts(combo=combo))
                except Exception as e: self._log('{}', e, level='error')
        self.setLayer(layer)
        fitView()
        return objs

    def make(self, copper_thickness=0.05, fit_arcs=True, load_parts=False, board_thickness=None, combo=True, fuseCoppers=False):
        self._pushLog('making pcb...', prefix='')
        if combo > 1: fuseCoppers = True
        objs = []
        board = self.makeBoard(prefix=None, thickness=board_thickness)
        if board: objs.append(board)

        coppers = self.makeCoppers(shape_type='solid', holes=True, prefix=None, fit_arcs=fit_arcs, thickness=copper_thickness, fuse=fuseCoppers, board_thickness=board_thickness)
        if coppers:
            if not fuseCoppers: objs += coppers
            else: objs.append(coppers)

        if load_parts: objs += self.loadAllParts(combo=True)

        if combo:
            layer = self.layer
            try:
                self.layer = None
                objs = self._makeGeneralFuse(objs, 'pcb') if combo > 1 else self._makeCompound(objs, 'pcb')
                if self.add_feature and load_parts and hasattr(objs, 'ViewObject'):
                    try: objs.ViewObject.SelectionStyle = 1
                    except Exception: pass
            finally:
                self.setLayer(layer)

        self._popLog('all done')
        fitView()
        return objs

def getTestFile(name):
    import glob
    if not os.path.exists(name):
        path = os.path.dirname(os.path.abspath(__file__))
        path = os.path.join(path, 'tests')
        if name: path = os.path.join(path, name)
    else: path = name
    if os.path.isdir(path): return glob.glob(os.path.join(path, '*.kicad_pcb'))
    if os.path.isfile(path): return [path]
    path += '.kicad_pcb'
    if os.path.isfile(path): return [path]
    raise RuntimeError('Cannot find {}'.format(name))

def test(names=''):
    if not isinstance(names, (tuple, list)): names = [names]
    files = set()
    for name in names: files.update(getTestFile(name))
    for f in files:
        pcb = KicadFcad(f)
        pcb.make()
        pcb.make(fuseCoppers=True)
        pcb.add_feature = False
        Part.show(pcb.make())