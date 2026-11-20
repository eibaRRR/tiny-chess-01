"""tiny-chess-01 entry: alpha-beta engine over HTTP env."""
import json, os, sys, urllib.request as U
E = os.environ["MAKEFUN_ENV_URL"]
WP, BP = "PNBRQK", "pnbrqk"
ND = (-21,-19,-12,-8,8,12,19,21)
BD = (-11,-9,9,11)
RD = (-10,10,-1,1)
QD = BD + RD
KD = QD
VAL = {"P":100,"N":320,"B":330,"R":500,"Q":900,"K":0}

def _sq(f,r): return 21+f+(8-r)*10
def _usq(s): return _sq("abcdefgh".index(s[0]), int(s[1]))
def _sqs(i): return "abcdefgh"[(i-21)%10] + str(8-(i-21)//10)

_PP = (0,0,0,0,0,0,0,0, 50,50,50,50,50,50,50,50, 10,10,20,30,30,20,10,10, 5,5,10,25,25,10,5,5, 0,0,0,20,20,0,0,0, 5,-5,-10,0,0,-10,-5,5, 5,10,10,-20,-20,10,10,5, 0,0,0,0,0,0,0,0)
_PN = (-50,-40,-30,-30,-30,-30,-40,-50, -40,-20,0,0,0,0,-20,-40, -30,0,10,15,15,10,0,-30, -30,5,15,20,20,15,5,-30, -30,0,15,20,20,15,0,-30, -30,5,10,15,15,10,5,-30, -40,-20,0,5,5,0,-20,-40, -50,-40,-30,-30,-30,-30,-40,-50)
_PB = (-20,-10,-10,-10,-10,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,10,10,5,0,-10, -10,5,5,10,10,5,5,-10, -10,0,10,10,10,10,0,-10, -10,10,10,10,10,10,10,-10, -10,5,0,0,0,0,5,-10, -20,-10,-10,-10,-10,-10,-10,-20)
_PR = (0,0,0,0,0,0,0,0, 5,10,10,10,10,10,10,5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, 0,0,0,5,5,0,0,0)
_PQ = (-20,-10,-10,-5,-5,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,5,5,5,0,-10, -5,0,5,5,5,5,0,-5, 0,0,5,5,5,5,0,-5, -10,5,5,5,5,5,0,-10, -10,0,5,0,0,0,0,-10, -20,-10,-10,-5,-5,-10,-10,-20)
_PK = (-30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -20,-30,-30,-40,-40,-30,-30,-20, -10,-20,-20,-20,-20,-20,-20,-10, 20,20,0,0,0,0,20,20, 20,30,10,0,0,10,30,20)
_PKE = (-50,-40,-30,-20,-20,-30,-40,-50, -30,-20,-10,0,0,-10,-20,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,20,30,30,20,-10,-30, -30,-30,0,0,0,0,-30,-30, -50,-30,-30,-30,-30,-30,-30,-50)
PST = {"P":_PP,"N":_PN,"B":_PB,"R":_PR,"Q":_PQ,"K":_PK}

def _pi(i):  return (i-21)//10*8 + (i-21)%10
def _pib(i): return (98-i)//10*8 + (i-21)%10

MATE = 100000
INF  = 1 << 30

def _load(fen):
    p = fen.split()
    b = [" "]*120
    for r in range(8):
        for f in range(8): b[21+r*10+f] = "."
    for r,row in enumerate(p[0].split("/")):
        f = 0
        for c in row:
            if c.isdigit(): f += int(c)
            else:
                b[21+r*10+f] = c; f += 1
    w = p[1] == "w"
    cr = set(x for x in p[2] if x in "KQkq")
    ep = 0 if p[3] == "-" else _usq(p[3])
    return [b,w,cr,ep]

_RK = {91:"Q", 98:"K", 21:"q", 28:"k", 95:"KQ", 25:"kq"}

def _attacked(b, sq, bywhite):
    if bywhite:
        if b[sq+9] == "P" or b[sq+11] == "P": return True
    else:
        if b[sq-9] == "p" or b[sq-11] == "p": return True
    pcs = WP if bywhite else BP
    kn = pcs[1]; kg = pcs[5]; bp = pcs[2]; rp = pcs[3]; qp = pcs[4]
    for d in ND:
        if b[sq+d] == kn: return True
    for d in KD:
        if b[sq+d] == kg: return True
    for d in BD:
        s = sq+d
        while b[s] == ".": s += d
        if b[s] == bp or b[s] == qp: return True
    for d in RD:
        s = sq+d
        while b[s] == ".": s += d
        if b[s] == rp or b[s] == qp: return True
    return False

def _king(b, white):
    kg = "K" if white else "k"
    for i in range(21,99):
        if b[i] == kg: return i
    return 0

def _gen(pos):
    b, w, cr, ep = pos
    out = []
    own = WP if w else BP
    enemy = BP if w else WP
    for i in range(21,99):
        p = b[i]
        if p == "." or p == " " or p not in own: continue
        pu = p.upper()
        if pu == "P":
            d = -10 if w else 10
            s2 = -20 if w else 20
            start_row_idx = 6 if w else 1
            promo_row_idx = 0 if w else 7
            row_i = (i-21)//10
            if b[i+d] == ".":
                if (i+d-21)//10 == promo_row_idx:
                    for pr in ("q","r","b","n"): out.append((i,i+d,pr))
                else:
                    out.append((i,i+d,""))
                    if row_i == start_row_idx and b[i+s2] == ".":
                        out.append((i,i+s2,""))
            for dc in (d-1, d+1):
                t = i+dc; tp = b[t]
                if tp == " ": continue
                if tp in enemy:
                    if (t-21)//10 == promo_row_idx:
                        for pr in ("q","r","b","n"): out.append((i,t,pr))
                    else:
                        out.append((i,t,""))
                elif ep and t == ep:
                    out.append((i,t,""))
        elif pu == "N":
            for d in ND:
                t = i+d; tp = b[t]
                if tp == " " or tp in own: continue
                out.append((i,t,""))
        elif pu == "K":
            for d in KD:
                t = i+d; tp = b[t]
                if tp == " " or tp in own: continue
                out.append((i,t,""))
            if w:
                if "K" in cr and b[96]=="." and b[97]=="." and b[98]=="R" and not _attacked(b,95,False) and not _attacked(b,96,False) and not _attacked(b,97,False):
                    out.append((95,97,""))
                if "Q" in cr and b[94]=="." and b[93]=="." and b[92]=="." and b[91]=="R" and not _attacked(b,95,False) and not _attacked(b,94,False) and not _attacked(b,93,False):
                    out.append((95,93,""))
            else:
                if "k" in cr and b[26]=="." and b[27]=="." and b[28]=="r" and not _attacked(b,25,True) and not _attacked(b,26,True) and not _attacked(b,27,True):
                    out.append((25,27,""))
                if "q" in cr and b[24]=="." and b[23]=="." and b[22]=="." and b[21]=="r" and not _attacked(b,25,True) and not _attacked(b,24,True) and not _attacked(b,23,True):
                    out.append((25,23,""))
        else:
            dirs = BD if pu == "B" else RD if pu == "R" else QD
            for d in dirs:
                t = i+d
                while True:
                    tp = b[t]
                    if tp == " " or tp in own: break
                    out.append((i,t,""))
                    if tp != ".": break
                    t += d
    return out

def _make(pos, mv):
    b, w, cr, ep = pos
    fr, to, pr = mv
    piece = b[fr]
    captured = b[to]
    pu = piece.upper()
    old_cr = set(cr)
    old_ep = ep
    new_ep = 0
    ep_cap_sq = 0; ep_cap_piece = "."
    if pu == "P" and ep and to == ep:
        ep_cap_sq = to + (10 if w else -10)
        ep_cap_piece = b[ep_cap_sq]
        b[ep_cap_sq] = "."
    if pu == "P" and abs(to-fr) == 20:
        new_ep = (fr+to)//2
    if pu == "P" and pr:
        piece = pr.upper() if w else pr
    rook_fr = rook_to = 0
    if pu == "K" and abs(to-fr) == 2:
        if to == 97: rook_fr, rook_to = 98, 96
        elif to == 93: rook_fr, rook_to = 91, 94
        elif to == 27: rook_fr, rook_to = 28, 26
        elif to == 23: rook_fr, rook_to = 21, 24
        b[rook_to] = b[rook_fr]; b[rook_fr] = "."
    b[to] = piece
    b[fr] = "."
    if fr in _RK:
        for ch in _RK[fr]: cr.discard(ch)
    if to in _RK:
        for ch in _RK[to]: cr.discard(ch)
    pos[1] = not w
    pos[3] = new_ep
    return (fr,to,captured,piece,pr,old_cr,old_ep,ep_cap_sq,ep_cap_piece,rook_fr,rook_to)

def _unmake(pos, u):
    fr,to,captured,piece,pr,old_cr,old_ep,ep_cap_sq,ep_cap_piece,rook_fr,rook_to = u
    b = pos[0]
    was_white = (pos[1] == False)
    if pr: b[fr] = "P" if was_white else "p"
    else:  b[fr] = piece
    b[to] = captured
    if ep_cap_sq: b[ep_cap_sq] = ep_cap_piece
    if rook_fr:
        b[rook_fr] = b[rook_to]; b[rook_to] = "."
    pos[1] = was_white
    pos[2] = old_cr
    pos[3] = old_ep

def _in_check(pos):
    b, w, cr, ep = pos
    return _attacked(b, _king(b, w), not w)

def _eval(pos):
    b, w, cr, ep = pos
    sw = sb = 0; phase = 0
    for i in range(21,99):
        p = b[i]
        if p == "." or p == " ": continue
        pu = p.upper()
        v = VAL[pu]
        if pu in ("N","B","R","Q"): phase += v
        if p.isupper(): sw += v + PST[pu][_pi(i)]
        else:           sb += v + PST[pu][_pib(i)]
    kw = _king(b, True); kb = _king(b, False)
    if phase < 2400:
        sw += _PKE[_pi(kw)]; sb += _PKE[_pib(kb)]
    else:
        sw += _PK[_pi(kw)];  sb += _PK[_pib(kb)]
    sc = sw - sb
    return sc if w else -sc

class Ctx:
    __slots__ = ("nodes","budget","killers","best","stop")
    def __init__(self, budget):
        self.nodes = 0; self.budget = budget
        self.killers = [[None,None] for _ in range(64)]
        self.best = None; self.stop = False

def _mvv(pos, mv):
    b = pos[0]; fr, to, pr = mv
    cap = b[to]
    if cap != ".": return 1000 + VAL.get(cap.upper(),0)*10 - VAL.get(b[fr].upper(),0)
    if pr: return 500 + VAL.get(pr.upper(),0)
    return 0

def _qs(pos, alpha, beta, ctx, ply):
    ctx.nodes += 1
    stand = _eval(pos)
    if stand >= beta: return beta
    if stand > alpha: alpha = stand
    moves = _gen(pos)
    caps = []
    b0 = pos[0]; ep0 = pos[3]
    for mv in moves:
        if b0[mv[1]] != "." or mv[2] or (b0[mv[0]].upper()=="P" and ep0 and mv[1]==ep0):
            caps.append(mv)
    caps.sort(key=lambda m: -_mvv(pos, m))
    for mv in caps:
        if ctx.nodes >= ctx.budget: ctx.stop = True; break
        u = _make(pos, mv)
        b2, wa = pos[0], pos[1]
        if _attacked(b2, _king(b2, not wa), wa):
            _unmake(pos, u); continue
        sc = -_qs(pos, -beta, -alpha, ctx, ply+1)
        _unmake(pos, u)
        if sc >= beta: return beta
        if sc > alpha: alpha = sc
    return alpha

def _search(pos, depth, alpha, beta, ctx, ply):
    ctx.nodes += 1
    if depth <= 0:
        return _qs(pos, alpha, beta, ctx, ply)
    moves = _gen(pos)
    k0, k1 = (ctx.killers[ply] if ply < 64 else (None,None))
    def key(m):
        s = -_mvv(pos, m)
        if m == k0: s -= 2000
        elif m == k1: s -= 1500
        return s
    moves.sort(key=key)
    legal = 0
    best = -INF
    for mv in moves:
        if ctx.stop and ply > 0 and legal > 0: break
        if ctx.nodes >= ctx.budget and ply > 0 and legal > 0:
            ctx.stop = True; break
        u = _make(pos, mv)
        b2, wa = pos[0], pos[1]
        if _attacked(b2, _king(b2, not wa), wa):
            _unmake(pos, u); continue
        legal += 1
        sc = -_search(pos, depth-1, -beta, -alpha, ctx, ply+1)
        _unmake(pos, u)
        if sc > best:
            best = sc
            if ply == 0: ctx.best = mv
        if sc > alpha: alpha = sc
        if alpha >= beta:
            b = pos[0]
            if b[mv[1]] == "." and not mv[2] and ply < 64 and k0 != mv:
                ctx.killers[ply] = [mv, k0]
            return alpha
    if legal == 0:
        if _in_check(pos): return -MATE + ply
        return 0
    return best

def choose(fen, legal_ucis, budget):
    pos = _load(fen)
    legal_set = set(legal_ucis)
    ctx = Ctx(budget)
    best_uci = None
    for depth in range(1, 40):
        ctx.nodes = 0
        ctx.stop = False
        ctx.best = None
        sc = _search(pos, depth, -INF, INF, ctx, 0)
        if ctx.stop:
            # discard partial-depth result
            break
        if ctx.best is not None:
            fr, to, pr = ctx.best
            u = _sqs(fr) + _sqs(to) + (pr if pr else "")
            if u in legal_set:
                best_uci = u
        if abs(sc) > MATE - 1000:
            break
    if best_uci:
        return best_uci
    def rk(m):
        b = _load(fen)[0]
        fr = _usq(m[:2]); to = _usq(m[2:4])
        cap = b[to]
        v = VAL.get(cap.upper(),0) if cap != "." else 0
        return (-v, m)
    return min(legal_ucis, key=rk)

def _post(path, body):
    req = U.Request(E + path, data=json.dumps(body).encode(),
                    headers={"content-type":"application/json"})
    with U.urlopen(req) as r:
        return json.load(r)

def main():
    budget = int(os.environ.get("TC_NODES", "270000"))
    while True:
        g = _post("/game", {})
        if g.get("status") == "done":
            print("done", g.get("wins"), g.get("draws"), g.get("losses"), file=sys.stderr)
            return
        while g.get("status") == "your_move":
            mv = choose(g["fen"], g["legal_moves"], budget)
            g = _post("/move", {"game": g["game"], "move": mv})
        print("game", g.get("game"), g.get("outcome"), g.get("reason"), file=sys.stderr)

main()
