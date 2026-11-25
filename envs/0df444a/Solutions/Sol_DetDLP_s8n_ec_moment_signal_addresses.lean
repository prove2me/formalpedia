-- Prove2me | solution 1 for DetDLP.s8n_ec_moment_signal_addresses
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T12:01:06.471798+00:00
-- url     : https://prove2.me/submissions/73764146-8c60-4859-b6b8-d6c3199a146f

import Definitions.Def_DetDLP_S8N_PortPoly
import Definitions.Def_DetDLP_S8N_AtomFixedAddresses
import Definitions.Def_DetDLP_S8M_StepBaseNat
import Definitions.Def_DetDLP_S8N_MomentSignalHash

section
set_option autoImplicit false

namespace DetDLP.S8N.MomentStepReuse
open Groundwork S8H.MakeCombinators S8H.PointAddresses S8M.EffCombinators
open S8M.StepBaseNat S8H4.TracksPoly S8H4.TracksRowsSpec S8N.MomentSignal
open private tileP from Definitions.Def_DetDLP_S8M_StepBaseNat

def stepEdges (d e : ℕ) := 170*(d+1)+15*(4*e+36*d+10)+31*d+5

/-- Input points are stored as a flag followed by two coordinate triples. -/
def stepTable (d e tip off left right : ℕ) : R :=
  (stepEdges d e, (S8M.StepBaseNat.tile d e tip left right off).2)

theorem stepLength (d e tip off left right : ℕ) :
    (stepTable d e tip off left right).1 = stepEdges d e := rfl

private theorem manyCount (n k : ℕ) (f : ℕ → NC) (h : ∀ j, (f j).1.ne = k) :
    (manyN n f).1.ne = (n+1)*k := by
  induction n generalizing f with
  | zero => simpa [manyN_zero] using h 0
  | succ n ih =>
    rw [manyN_succ]
    change (f 0).1.ne + (manyN n (fun j => f (j+1))).1.ne = _
    rw [h 0,ih _ (fun j => h (j+1))]
    ring

private theorem hashCount (d e tip o aux : ℕ) (a x b : ℕ → ℕ) :
    (hashN d e tip o aux a x b).1.ne = 4*wires d+36*d+10 := by
  simp only [hashN,genHashN,prodN,catN,sum,colN,add,rowN,S8H0.BaseCode.rowsCode,S8H.PointAddresses.mul]
  omega

/-- The numeric core always counts the edge geometry of its own multiplier. -/
theorem coreLength (d e tip off left right : ℕ) :
    (S8M.StepBaseNat.tile d e tip left right off).1.ne = stepEdges d (wires d) := by
  unfold S8M.StepBaseNat.tile
  dsimp only
  have catCount (a b : NC) : (catN a b).1.ne = a.1.ne+b.1.ne := rfl
  simp only [catCount]
  rw [manyCount 3 ((d+1)*5) _ (fun _ => rfl)]
  rw [manyCount 14 ((d+1)*5+(d+1)*5) _ (fun _ => rfl)]
  rw [manyCount 14 (4*wires d+36*d+10) _ (fun _ => hashCount ..)]
  simp only [rowN,S8H0.BaseCode.rowsCode,stepEdges]
  omega

attribute [local fun_prop] PolyT.const PolyT.add PolyT.mul

theorem stepGood {α : Type} [Enc α] {d e tip off left right : α → ℕ}
    (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off)
    (hl : PolyT left) (hr : PolyT right) :
    Good fun z => stepTable (d z) (e z) (tip z) (off z) (left z) (right z) := by
  have p := tileP hd he ht hl hr ho
  refine ⟨?_, fun _ hj => (p.2.2 hj).2⟩
  change PolyT (fun z => 170*(d z+1)+15*(4*e z+36*d z+10)+31*d z+5)
  fun_prop (disch := assumption)

end DetDLP.S8N.MomentStepReuse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.MomentStepProof.ContiguousHashFit
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators
open private gw fstP sndP rwrd refw from Definitions.Def_DetDLP_S8N_ECAddRoutes

private theorem idxL {s t : Shape} (a : Addr s) : (Addr.fst (v:=t) a).index.val = a.index.val := rfl
private theorem idxR {s t : Shape} (a : Addr t) : (Addr.snd (u:=s) a).index.val = s.size + a.index.val := rfl

theorem addHashFits {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p o : ℕ)
    (path : Path (ECMapRows.slot d (Routes.G hd)) s)
    (hor : ∀ a, (path a).index.val = o + a.index.val)
    {a x b : ℕ → ℕ} {A X B : Word s}
    (ha : Names a A) (hx : Names x X) (hb : Names b B) :
    Fits (StepBaseNat.hashN d (Routes.G hd) s.size o (o + 11*d+2*(Routes.G hd)+3) a x b)
      (HashRows.block p (gw hd p A X B path)) := by
  have reg (j : Addr (ECMapRows.slot d (Routes.G hd))) :
      (Ref.reg (path j)).source.val = o+j.index.val := hor j
  have masked (v : Bool) (j : Addr (ECMapRows.slot d (Routes.G hd))) :
      (Ref.masked v (path j)).source.val = o+j.index.val := hor j
  apply genHash_spec p _ ha hx hb
  all_goals intro j
  all_goals dsimp only [gw, fstP, sndP, rwrd, refw, wd, word, padded, pad]
  all_goals (try split_ifs) <;> first
    | rfl
    | erw [reg]
    | erw [masked]
    | (rename_i hn; exact (hn (show j.val < Routes.G hd from j.isLt)).elim)
  all_goals simp only [idxL, idxR, Shape.size, RegisterMap.mul, triple, run, auxShape,
    Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd]
  all_goals omega

end DetDLP.S8M.MomentStepProof.ContiguousHashFit

namespace DetDLP.S8M.MomentStepProof.MapAddressRows
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes S8H.MakeCombinators EffCombinators
open private rwrd fstP from Definitions.Def_DetDLP_S8M_ECMapRows

theorem wordNames {d o : ℕ} {s : Shape} (path : Path (triple d) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) :
    Names (wd o d s.size) (rwrd path) := by
  intro j
  dsimp only [wd, rwrd, fstP, word, padded]
  split_ifs with hj
  · exact (h (.fst (.word ⟨j,hj⟩))).symm
  · rfl

theorem rangeFits {d o : ℕ} {s : Shape} (p : ℕ) (path : Path (triple d) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) :
    Fits (rangeN d s.size o) (checker p path) := by
  apply col_spec
  · intro i
    unfold wd RangeRows.pad
    split_ifs with hi
    · exact (h (.fst (.word ⟨i,hi⟩))).symm
    · rfl
  · intro i
    unfold wd RangeRows.pad
    split_ifs with hi
    · exact (Nat.add_assoc ..).trans (h (.snd (.fst (.word ⟨i,hi⟩)))).symm
    · rfl
  · intro i; rfl
  · intro i
    have v := (h (.snd (.snd (.word i)))).symm
    change o+(d+(d+i.val)) = _ at v
    exact (by omega : o+2*d+i.val = o+(d+(d+i.val))).trans v

end DetDLP.S8M.MomentStepProof.MapAddressRows

namespace DetDLP.S8M.MomentStepProof.AddAddressRows
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators S8N.ECAddRoutes
open private regP sl flag slope res remP fstP sndP rwrd from Definitions.Def_DetDLP_S8N_ECAddRoutes

def coord (o d k : ℕ) := o+1+k*(3*d+1)
def flags (o d : ℕ) := coord o d 4
def slopeOff (o d : ℕ) := flags o d+2
def hashOff (o d e k : ℕ) := slopeOff o d+d+k*(16*d+2*e+6)

variable {d e o : ℕ} {s : Shape} (path : Path (addShape d e) s)
variable (h : ∀ a, (path a).index.val = o+a.index.val)
include h

theorem regOffset (k : Fin 4) (a : Addr (triple d)) :
    ((regP path k) a).index.val = coord o d k+a.index.val := by
  erw [h]
  dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, EquivLike.coe, DFunLike.coe,
    EquivLike.toFunLike, Equiv.instEquivLike, finProdFinEquiv, Shape.size, triple, coord]
  ring

theorem slotOffset (k : Fin 15) (a : Addr (ECMapRows.slot d e)) :
    ((sl path k) a).index.val = hashOff o d e k+a.index.val := by
  erw [h]
  dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, EquivLike.coe, DFunLike.coe,
    EquivLike.toFunLike, Equiv.instEquivLike, finProdFinEquiv, Shape.size,
    ECMapRows.slot, auxShape, RegisterMap.mul, triple, run, coord, flags, slopeOff, hashOff]
  ring

theorem flagName (k : Fin 2) : flags o d + k.val = (flag path k).source.val := by
  change _ = (path _).index.val
  erw [h]
  dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, EquivLike.coe, DFunLike.coe,
    EquivLike.toFunLike, Equiv.instEquivLike, finProdFinEquiv, Shape.size, triple, coord, flags]
  ring

theorem slopeNames : Names (wd (slopeOff o d) d s.size) (word (slope path)) := by
  intro j
  dsimp only [wd, word, padded]
  split_ifs with hj
  · change _ = (path _).index.val
    erw [h]
    dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple, coord, flags, slopeOff]
    omega
  · rfl

theorem coordNames (k : Fin 4) : Names (wd (coord o d k) d s.size) (rwrd (regP path k)) :=
  MapAddressRows.wordNames _ (regOffset path h k)

theorem resultNames (k : Fin 15) : Names (wd (hashOff o d e k) d s.size) (rwrd (res (sl path k))) := by
  apply MapAddressRows.wordNames
  intro a
  exact slotOffset path h k (.fst (.fst a))

theorem coordRanges (p : ℕ) :
    Fits (manyN 3 fun k => rangeN d s.size (coord o d k))
      (many 3 fun k => checker p (regP path k)) := by
  apply manyN_spec
  intro k
  exact MapAddressRows.rangeFits p _ (regOffset path h k)

theorem hashRanges (p : ℕ) :
    Fits (manyN 14 fun k => catN (rangeN d s.size (hashOff o d e k))
      (rangeN d s.size (hashOff o d e k+(3*d+1))))
      (many 14 fun k => joinB (checker p (res (sl path k))) (checker p (remP (sl path k)))) := by
  apply manyN_spec
  intro k
  apply cat_spec <;> apply MapAddressRows.rangeFits <;> intro a
  all_goals dsimp only [res, remP, fstP, sndP]
  all_goals erw [slotOffset path h]
  all_goals dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
  all_goals omega

end DetDLP.S8M.MomentStepProof.AddAddressRows

namespace DetDLP.S8M.MomentStepProof.AddOperandNames
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes S8N.ECAddRoutes
open S8H.MakeCombinators EffCombinators StepBaseNat AddAddressRows
open private regP sl slope res rwrd from Definitions.Def_DetDLP_S8N_ECAddRoutes

private theorem argsRel {α β : Type} (r : α → β → Prop)
    {n one t c z x y X Y l : α} {a : Fin 4 → α} {b : Fin 15 → α}
    {n' one' t' c' z' x' y' X' Y' l' : β} {a' : Fin 4 → β} {b' : Fin 15 → β}
    (hn : r n n') (ho : r one one') (ht : r t t') (hc : r c c') (hz : r z z')
    (hx : r x x') (hy : r y y') (hX : r X X') (hY : r Y Y') (hl : r l l')
    (ha : ∀ j, r (a j) (a' j)) (hb : ∀ j, r (b j) (b' j)) (g : Fin 15) :
    let u := args n one t c z x y X Y l a b g
    let v := args n' one' t' c' z' x' y' X' Y' l' a' b' g
    r u.1 v.1 ∧ r u.2.1 v.2.1 ∧ r u.2.2 v.2.2 := by
  fin_cases g <;> refine ⟨?_,?_,?_⟩ <;> first | assumption | apply ha | apply hb

theorem names {d e o u v : ℕ} {s : Shape} (path : Path (addShape d e) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) (neg1 three c4 : ℕ)
    {xp yp xq yq : Word s} (hx : Names (wd (u+1) d s.size) xp)
    (hy : Names (wd (u+1+(3*d+1)) d s.size) yp)
    (hX : Names (wd (v+1) d s.size) xq) (hY : Names (wd (v+1+(3*d+1)) d s.size) yq) (g : Fin 15) :
    let op := operand d e s.size u v o
    let a := fun k => rwrd (regP path k)
    let b := fun k => rwrd (res (sl path k))
    let r := args (pub neg1) (pub 1) (pub three) (pub c4) (pub 0) xp yp xq yq (word (slope path)) a b g
    Names (op (tags g.val).1) r.1 ∧ Names (op (tags g.val).2.1) r.2.1 ∧ Names (op (tags g.val).2.2) r.2.2 := by
  let op := operand d e s.size u v o
  let rel := fun (k : ℕ) (w : Word s) => Names (op k) w
  have hp (n : ℕ) : rel 0 (pub n) := fun _ => rfl
  have ac (k : Fin 4) : rel (6+k.val) (rwrd (regP path k)) := by
    intro j
    have v : op (6+k.val) j = wd (coord o d k) d s.size j := by fin_cases k <;> rfl
    exact v.trans (coordNames path h k j)
  have ar (k : Fin 15) : rel (10+k.val) (rwrd (res (sl path k))) := by
    intro j
    have v : op (10+k.val) j = wd (hashOff o d e k) d s.size j := by fin_cases k <;> rfl
    exact v.trans (resultNames path h k j)
  have eqg : Fin.ofNat 15 g.val = g := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt g.isLt
  unfold tags
  rw [eqg]
  exact argsRel (n:=0) (one:=0) (t:=0) (c:=0) (z:=0)
    (x:=1) (y:=2) (X:=3) (Y:=4) (l:=5) (a:=fun k => 6+k.val) (b:=fun k => 10+k.val)
    (x':=xp) (y':=yp) (X':=xq) (Y':=yq) rel (hp neg1) (hp 1) (hp three) (hp c4) (hp 0)
    hx hy hX hY (slopeNames path h) ac ar g

end DetDLP.S8M.MomentStepProof.AddOperandNames

namespace DetDLP.S8M.MomentStepProof.AddControlRows
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes S8N.ECAddRoutes
open S8H.MakeCombinators EffCombinators
open private invRows selectRows from Definitions.Def_DetDLP_S8N_ECAddRoutes

private theorem bitName {d o : ℕ} {s : Shape} {w : Word s} (h : Names (wd o d s.size) w)
    (i : Fin d) : o+i.val = (w i.val).source.val := by
  simpa only [wd, if_pos i.isLt] using h i.val

def inverseCode (d f a v r : ℕ) : NC :=
  rowN d 4 fun j t => if t=0 then f else if t=1 then a+j else if t=2 then v+j else r+j

theorem inverseFit {d f a v r : ℕ} {s : Shape} {flag : Ref s} {A V R : Word s}
    (hf : f = flag.source.val) (ha : Names (wd a d s.size) A)
    (hv : Names (wd v d s.size) V) (hr : Names (wd r d s.size) R) :
    Fits (inverseCode d f a v r) (invRows d flag A V R) := by
  apply row_spec
  intro i k
  fin_cases k
  · exact hf
  · exact bitName ha i
  · exact bitName hv i
  · exact bitName hr i

def head (u v f t : ℕ) := if t=0 then u else if t=1 then v else if t=2 then f else f+1

def slopeCode (d u v f x y l : ℕ) : NC :=
  rowN d 7 fun j t => if t<4 then head u v f t else if t=4 then x+j else if t=5 then y+j else l+j

theorem slopeFit {d u v f x y l : ℕ} {s : Shape} {U V F G : Ref s} {X Y L : Word s}
    (hu : u = U.source.val) (hv : v = V.source.val)
    (hf : f = F.source.val) (hg : f+1 = G.source.val)
    (hx : Names (wd x d s.size) X) (hy : Names (wd y d s.size) Y)
    (hl : Names (wd l d s.size) L) (test : Fin d → (Fin 7 → Bool) → Bool) :
    Fits (slopeCode d u v f x y l)
      (rows d 7 (fun k => ![U,V,F,G,X k,Y k,L k]) test) := by
  apply row_spec
  intro i k
  fin_cases k
  · exact hu
  · exact hv
  · exact hf
  · exact hg
  · exact bitName hx i
  · exact bitName hy i
  · exact bitName hl i

def flagCode (u v f o : ℕ) : NC :=
  rowN 1 5 fun _ t => if t<4 then head u v f t else o

theorem flagFit {u v f o : ℕ} {s : Shape} {U V F G O : Ref s}
    (hu : u = U.source.val) (hv : v = V.source.val) (hf : f = F.source.val)
    (hg : f+1 = G.source.val) (ho : o = O.source.val) (test : Fin 1 → (Fin 5 → Bool) → Bool) :
    Fits (flagCode u v f o) (rows 1 5 (fun _ => ![U,V,F,G,O]) test) := by
  apply row_spec
  intro i k
  fin_cases k
  · exact hu
  · exact hv
  · exact hf
  · exact hg
  · exact ho

def selectCode (d u v f ubit vbit z o : ℕ) : NC :=
  rowN d 8 fun j t => if t<4 then head u v f t else if t=4 then ubit+j
    else if t=5 then vbit+j else if t=6 then z+j else o+j

theorem selectFit {d u v f ubit vbit z o : ℕ} {s : Shape} {U V F G : Ref s} {A B Z O : Word s}
    (hu : u = U.source.val) (hv : v = V.source.val) (hf : f = F.source.val)
    (hg : f+1 = G.source.val) (ha : Names (wd ubit d s.size) A) (hb : Names (wd vbit d s.size) B)
    (hz : Names (wd z d s.size) Z) (ho : Names (wd o d s.size) O) :
    Fits (selectCode d u v f ubit vbit z o) (selectRows d U V F G A B Z O) := by
  apply row_spec
  intro i k
  fin_cases k
  · exact hu
  · exact hv
  · exact hf
  · exact hg
  · exact bitName ha i
  · exact bitName hb i
  · exact bitName hz i
  · exact bitName ho i

end DetDLP.S8M.MomentStepProof.AddControlRows

namespace DetDLP.S8M.MomentStepProof.RealAddTile
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes S8N.ECAddRoutes
open S8H.MakeCombinators EffCombinators StepBaseNat AddAddressRows AddControlRows
open private regP sl flag slope res rwrd gw from Definitions.Def_DetDLP_S8N_ECAddRoutes

def hashCode (d e pin u v o k : ℕ) : NC :=
  let z := hashOff o d e k
  let op := operand d e pin u v o
  hashN d e pin z (z+11*d+2*e+3) (op (tags k).1) (op (tags k).2.1) (op (tags k).2.2)

attribute [local irreducible] Fits catN manyN rowN rangeN colN genHashN
  joinB RangeRows.many HashRows.block

theorem hashRows {d o u v : ℕ} {s : Shape} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (path : Path (addShape d (Routes.G hd)) s) (h : ∀ a, (path a).index.val = o+a.index.val)
    {xp yp xq yq : Word s} (hx : Names (wd (u+1) d s.size) xp)
    (hy : Names (wd (u+1+(3*d+1)) d s.size) yp)
    (hX : Names (wd (v+1) d s.size) xq) (hY : Names (wd (v+1+(3*d+1)) d s.size) yq) :
    let a := fun k => rwrd (regP path k)
    let r := fun k => rwrd (res (sl path k))
    let g := args (pub neg1) (pub 1) (pub three) (pub c4) (pub 0) xp yp xq yq (word (slope path)) a r
    Fits (manyN 14 (hashCode d (Routes.G hd) s.size u v o))
      (many 14 fun k => HashRows.block p (gw hd p (g k).1 (g k).2.1 (g k).2.2 (sl path k))) := by
  dsimp only
  apply manyN_spec
  intro k
  obtain ⟨ha,hb,hc⟩ := AddOperandNames.names path h neg1 three c4 hx hy hX hY k
  exact ContiguousHashFit.addHashFits hd p _ _ (slotOffset path h k) ha hb hc

theorem tileFits {d o u v : ℕ} {s : Shape} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (path : Path (addShape d (Routes.G hd)) s) (h : ∀ a, (path a).index.val = o+a.index.val)
    {fp fq : Ref s} {xp yp xq yq : Word s}
    (hu : u = fp.source.val) (hv : v = fq.source.val)
    (hx : Names (wd (u+1) d s.size) xp) (hy : Names (wd (u+1+(3*d+1)) d s.size) yp)
    (hX : Names (wd (v+1) d s.size) xq) (hY : Names (wd (v+1+(3*d+1)) d s.size) yq) :
    Fits (tile d (Routes.G hd) s.size u v o) (addBlock hd p neg1 three c4 fp xp yp fq xq yq path) := by
  have f0 : flags o d = (flag path 0).source.val := flagName path h 0
  have f1 : flags o d + 1 = (flag path 1).source.val := flagName path h 1
  have fo : o = (Ref.reg (path (.fst (.fst .bit)))).source.val := by
    change o = (path _).index.val
    erw [h]
    rfl
  let a := coordNames path h
  let r := resultNames path h
  have hs := slopeNames path h
  have ux : Names (wd (u+1+0*(3*d+1)) d s.size) xp := by simpa using hx
  have vx : Names (wd (v+1+0*(3*d+1)) d s.size) xq := by simpa using hX
  have uy : Names (wd (u+1+1*(3*d+1)) d s.size) yp := by simpa using hy
  have vy : Names (wd (v+1+1*(3*d+1)) d s.size) yq := by simpa using hY
  refine cat_spec (coordRanges path h p) <| cat_spec (hashRanges path h p) <|
    cat_spec (hashRows hd p neg1 three c4 path h hx hy hX hY) <|
    cat_spec (inverseFit f0 (r 0) (a 2) (r 1)) <| cat_spec (inverseFit f1 (r 2) (a 3) (r 3)) <|
    cat_spec (slopeFit hu hv f0 f1 (r 5) (r 8) hs _) <| cat_spec (flagFit hu hv f0 f1 fo _) <|
    cat_spec (selectFit hu hv f0 f1 ux vx (r 11) (a 0)) (selectFit hu hv f0 f1 uy vy (r 14) (a 1))

end DetDLP.S8M.MomentStepProof.RealAddTile

namespace DetDLP.S8N.MomentStepReuse
open S8H0 RegisterMap NamedBlocks HashRows GateRoutes S8N.ECAddRoutes
open S8H.MakeCombinators S8M.EffCombinators S8H4.TracksRowsSpec S8N.MomentSignal

abbrev PointRef (s : Shape) := Ref s × Word s × Word s
abbrev PointAt {s : Shape} (d base : ℕ) (r : PointRef s) :=
  base = r.1.source.val ∧ WordAt (wd (base+1) d s.size) r.2.1 ∧
    WordAt (wd (base+1+(3*d+1)) d s.size) r.2.2

theorem stepTracks {d left right off : ℕ} {s : Shape} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (path : Path (addShape d (S8M.Routes.G hd)) s) (hp : PathAt path off)
    {a b : PointRef s} (ha : PointAt d left a) (hb : PointAt d right b) :
    Tracks (stepTable d (S8M.Routes.G hd) s.size off left right)
      (addBlock hd p neg1 three c4 a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2 path) := by
  have fits := S8M.MomentStepProof.RealAddTile.tileFits hd p neg1 three c4 path hp
    ha.1 hb.1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  refine ⟨?_,fits.2⟩
  have h := coreLength d (S8M.Routes.G hd) s.size off left right
  rw [S8H.PointAddresses.wires_eq hd] at h
  exact h.symm.trans fits.1.ne

end DetDLP.S8N.MomentStepReuse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8N.MomentStepReuse
open Groundwork S8H0 RegisterMap NamedBlocks HashRows GateRoutes
open S8H4.TracksPoly S8H4.TracksRowsSpec S8N.MomentSignal S8M.EffCombinators
open S8N.ECAddRoutes S8M.ECFoldRoutes
open private slice outFlag outX outY outputFlag outputX outputY foldStep from Definitions.Def_DetDLP_S8M_ECFoldRoutes

def slotStart (d e off i : ℕ) := off+(253*d+30*e+97)*i
def previous (d e off initial i : ℕ) := if i=0 then initial else slotStart d e off (i-1)
def pairRows (n left right : ℕ) : R :=
  rowTable n 2 fun j k => (if k=0 then left else right)+j

/-- Fold a group of contiguous points into a target that is also stored in the register bank. -/
def foldTable (n d e tip off initial target : ℕ) (points : ℕ → ℕ) : R :=
  let last := previous d e off initial n
  let y := fun base => base+1+(3*d+1)
  cat (pairRows 1 last target) <| cat (pairRows d (last+1) (target+1)) <|
    cat (pairRows d (y last) (y target)) <|
      tileTable n (stepEdges d e) fun i =>
        stepTable d e tip (slotStart d e off i) (previous d e off initial i) (points i)

theorem foldLength (n d e tip off initial target : ℕ) (points : ℕ → ℕ) :
    (foldTable n d e tip off initial target points).1 = 2+4*d+n*stepEdges d e := by
  change 1*2+(d*2+(d*2+n*stepEdges d e)) = _
  omega

private theorem sliceAt {n d e off : ℕ} {s : Shape} (f : Path (foldShape n d e) s)
    (h : PathAt f off) (i : Fin n) : PathAt (slice f i) (slotStart d e off i.val) := by
  simpa only [slotStart,S8M.StepBaseNat.add_size] using pathVec (l:=addShape d e) h i

private theorem storedOutput {n d e off : ℕ} {s : Shape} (f : Path (foldShape n d e) s)
    (h : PathAt f off) (i : Fin n) :
    PointAt d (slotStart d e off i.val) (outFlag f i,outX f i,outY f i) := by
  let base := slotStart d e off i.val
  have hs := sliceAt f h i
  refine ⟨?_,?_,?_⟩
  · change base = (slice f i _).index.val
    erw [hs]; rfl
  · simpa [S8M.MomentStepProof.AddAddressRows.coord] using
      S8M.MomentStepProof.AddAddressRows.coordNames (slice f i) hs 0
  · simpa [S8M.MomentStepProof.AddAddressRows.coord] using
      S8M.MomentStepProof.AddAddressRows.coordNames (slice f i) hs 1

private theorem pairTracks {n left right : ℕ} {s : Shape}
    (a b : Fin n → Ref s) (ha : ∀ i : Fin n, left+i.val = (a i).source.val)
    (hb : ∀ i : Fin n, right+i.val = (b i).source.val) (test : Fin n → (Fin 2 → Bool) → Bool) :
    Tracks (pairRows n left right) (rows n 2 (fun i => ![a i,b i]) test) := by
  apply rowTracks
  intro i k
  fin_cases k
  · exact ha i
  · exact hb i

attribute [local irreducible] Tracks stepTable

set_option maxHeartbeats 450000 in
theorem foldTracks {n d off initial target : ℕ} {s : Shape} (hd : 1 ≤ d) (p neg three c4 : ℕ)
    (f : Path (foldShape n d (S8M.Routes.G hd)) s) (h : PathAt f off)
    (points : ℕ → ℕ) (a t : PointRef s) (b : Fin n → PointRef s)
    (ha : PointAt d initial a) (ht : PointAt d target t) (hb : ∀ i : Fin n, PointAt d (points i.val) (b i)) :
    Tracks (foldTable n d (S8M.Routes.G hd) s.size off initial target points)
      (foldBlock hd p neg three c4 a.1 a.2.1 a.2.2 (fun i => (b i).1)
        (fun i => (b i).2.1) (fun i => (b i).2.2) t.1 t.2.1 t.2.2 f) := by
  let e := S8M.Routes.G hd
  have last : PointAt d (previous d e off initial n) (outputFlag a.1 f,outputX a.2.1 f,outputY a.2.2 f) := by
    by_cases h0 : n=0
    · simpa only [previous,if_pos h0,outputFlag,outputX,outputY,dif_pos h0] using ha
    · simpa only [previous,if_neg h0,outputFlag,outputX,outputY,dif_neg h0] using
        storedOutput f h (⟨n-1,by omega⟩ : Fin n)
  unfold foldTable foldBlock
  refine cat_ok (pairTracks _ _ ?_ ?_ _) <| cat_ok (pairTracks _ _ ?_ ?_ _) <|
    cat_ok (pairTracks _ _ ?_ ?_ _) <| tileTracks _ _ _ _ (fun _ => stepLength ..) (fun i => ?_)
  · intro i; rw [show i.val=0 by omega, Nat.add_zero]; exact last.1
  · intro i; rw [show i.val=0 by omega, Nat.add_zero]; exact ht.1
  · intro i; simpa only [S8M.EffCombinators.wd,if_pos i.isLt] using last.2.1 i.val
  · intro i; simpa only [S8M.EffCombinators.wd,if_pos i.isLt] using ht.2.1 i.val
  · intro i; simpa only [S8M.EffCombinators.wd,if_pos i.isLt] using last.2.2 i.val
  · intro i; simpa only [S8M.EffCombinators.wd,if_pos i.isLt] using ht.2.2 i.val
  · unfold foldStep
    by_cases h0 : i.val=0
    · simp only [previous,if_pos h0,dif_pos h0]
      exact stepTracks (a:=a) (b:=b i) hd p neg three c4 _ (sliceAt f h i) ha (hb i)
    · simp only [previous,if_neg h0,dif_neg h0]
      let j : Fin n := ⟨i.val-1,by have := i.isLt; omega⟩
      exact stepTracks (a:=(outFlag f j,outX f j,outY f j)) (b:=b i)
        hd p neg three c4 _ (sliceAt f h i) (storedOutput f h j) (hb i)

attribute [local fun_prop] PolyT.const PolyT.mul PolyT.add PolyT.sub PolyT.decide_eq PolyT.ite'

private theorem slotGood {α : Type} [Enc α] {d e off i : α → ℕ}
    (hd : PolyT d) (he : PolyT e) (ho : PolyT off) (hi : PolyT i) :
    PolyT fun x => slotStart (d x) (e x) (off x) (i x) := by
  unfold slotStart; fun_prop (disch := assumption)

private theorem previousGood {α : Type} [Enc α] {d e off i initial : α → ℕ}
    (hd : PolyT d) (he : PolyT e) (ho : PolyT off) (hi : PolyT i) (h0 : PolyT initial) :
    PolyT fun x => previous (d x) (e x) (off x) (initial x) (i x) :=
  PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) h0 (slotGood hd he ho (PolyT.sub hi (PolyT.const 1)))

private theorem pairGood {α : Type} [Enc α] {n a b : α → ℕ} (hn : PolyT n) (ha : PolyT a) (hb : PolyT b) :
    Good fun x => pairRows (n x) (a x) (b x) := by
  apply rowGood hn (PolyT.const 2)
  intro i j hi hj
  exact PolyT.add (PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) ha hb) hi

theorem foldGood {α : Type} [Enc α] {n d e tip off initial target : α → ℕ} {points : α → ℕ → ℕ}
    (hn : PolyT n) (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off)
    (ha : PolyT initial) (hz : PolyT target) (hp : WordCode points) :
    Good fun x => foldTable (n x) (d x) (e x) (tip x) (off x) (initial x) (target x) (points x) := by
  have last := previousGood hd he ho hn ha
  have tr := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  have edges : PolyT fun x => stepEdges (d x) (e x) := by unfold stepEdges; fun_prop (disch := assumption)
  exact catGood (pairGood (PolyT.const 1) last hz) (catGood (pairGood hd
    (PolyT.add last (PolyT.const 1)) (PolyT.add hz (PolyT.const 1))) (catGood (pairGood hd
      (PolyT.add (PolyT.add last (PolyT.const 1)) tr) (PolyT.add (PolyT.add hz (PolyT.const 1)) tr))
      (tileGood hn edges (fun j hj => stepGood hd he ht (slotGood hd he ho hj) (previousGood hd he ho hj ha) (hp hj)))))

end DetDLP.S8N.MomentStepReuse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.S8N.MomentStepReuse
open Groundwork S8H0 RegisterMap NamedBlocks HashRows GateRoutes
open S8H4.TracksPoly S8H4.TracksRowsSpec S8N.MomentSignal S8M.EffCombinators
open S8M.ECMapRows S8M.ECFoldRoutes S8G.SeedAndAtomBank
open private firstIndex_lt foldIndex_lt from Definitions.Def_DetDLP_S8N_Routes_v3

def mapBase (d e off i : ℕ) := off+(6*d+3)+(70*d+8*e+27)*i
def foldBase (m d e off k : ℕ) :=
  off+(6*d+3)+(2*m)*(70*d+8*e+27)+((m-1)*(253*d+30*e+97))*k
def groupEdges (m d e : ℕ) := 2+4*d+(m-1)*stepEdges d e

/-- The left and right groups each begin at their own map output. Both folds
    compare their last value to the same stored target. -/
def productFolds (m d e tip off : ℕ) : R :=
  tileTable 2 (groupEdges m d e) fun k =>
    foldTable (m-1) d e tip (foldBase m d e off k) (mapBase d e off (k*m)) off
      (fun i => mapBase d e off (k*m+i+1))

theorem productFoldsLength (m d e tip off : ℕ) :
    (productFolds m d e tip off).1 = 2*(2+4*d+(m-1)*stepEdges d e) := rfl

private theorem targetSize (d : ℕ) : (RoutesV2.targetShape d).size = 6*d+3 := by
  simp only [RoutesV2.targetShape,Shape.size,triple]; omega

private theorem targetPoint {d off : ℕ} {s : Shape} (f : Path (RoutesV2.targetShape d) s) (h : PathAt f off) :
    PointAt d off (RoutesV2.targetFlag f,RoutesV2.targetX f,RoutesV2.targetY f) := by
  refine ⟨?_,pathWord _ _ (pathFst (pathFst (pathSnd h))),?_⟩
  · change off = (f (.fst .bit)).index.val
    erw [h]; rfl
  · change WordAt (S8H4.TracksPoly.pad d s.size (off+1+triSize d))
      (word fun a : Addr (.word d) => f (.snd (.snd (.fst a))))
    simpa only [Shape.size,triSize_eq] using pathWord _ _ (pathFst (pathSnd (pathSnd h)))

private theorem mappedPoint {m d e off : ℕ} {s : Shape}
    (f : Path (RoutesV2.productShape m d e) s) (h : PathAt f off) (j : Fin (2*m)) :
    let a := RoutesV2.mapPath f j
    PointAt d (mapBase d e off j.val) (RoutesV2.mapFlag a,RoutesV2.mapX a,RoutesV2.mapY a) := by
  have hmap : PathAt (RoutesV2.mapPath f j) (mapBase d e off j.val) := by
    change PathAt (fun a => f (.snd (.fst (.vec j a)))) _
    simpa only [mapBase,targetSize,S8M.AtomMapNat.map_size] using pathVec (pathFst (pathSnd h)) j
  exact targetPoint (fun a => RoutesV2.mapPath f j (.fst a)) (pathFst hmap)

attribute [local irreducible] Tracks foldTable

set_option maxHeartbeats 500000 in
theorem productFoldsTracks {m d off : ℕ} {s : Shape} (hm : 1 ≤ m) (hd : 1 ≤ d)
    (p neg three c4 : ℕ) (f : Path (RoutesV2.productShape m d (S8M.Routes.G hd)) s) (h : PathAt f off) :
    Tracks (productFolds m d (S8M.Routes.G hd) s.size off)
      (allRows 2 fun k =>
        let a := RoutesV2.mapPath f ⟨k.val*m,firstIndex_lt hm k⟩
        let t := RoutesV2.target f
        foldBlock hd p neg three c4 (RoutesV2.mapFlag a) (RoutesV2.mapX a) (RoutesV2.mapY a)
          (RoutesV2.foldFlag hm f k) (RoutesV2.foldX hm f k) (RoutesV2.foldY hm f k)
          (RoutesV2.targetFlag t) (RoutesV2.targetX t) (RoutesV2.targetY t) (RoutesV2.foldPath f k)) := by
  let e := S8M.Routes.G hd
  apply tileTracks
  · intro k; exact foldLength ..
  · intro k
    have atFold : PathAt (RoutesV2.foldPath f k) (foldBase m d e off k.val) := by
      change PathAt (fun a => f (.snd (.snd (.vec k a)))) _
      simpa only [foldBase,foldShape,Shape.size,targetSize,S8M.AtomMapNat.map_size,S8M.StepBaseNat.add_size]
        using pathVec (pathSnd (pathSnd h)) k
    let a := (⟨k.val*m,firstIndex_lt hm k⟩ : Fin (2*m))
    let b (i : Fin (m-1)) := (⟨k.val*m+i.val+1,foldIndex_lt hm k i⟩ : Fin (2*m))
    let mapped (i : Fin (2*m)) : PointRef s :=
      (RoutesV2.mapFlag (RoutesV2.mapPath f i), RoutesV2.mapX (RoutesV2.mapPath f i),
        RoutesV2.mapY (RoutesV2.mapPath f i))
    let dst := RoutesV2.target f
    exact foldTracks (initial:=mapBase d e off (k.val*m)) (target:=off) hd p neg three c4
      (RoutesV2.foldPath f k) atFold (fun i => mapBase d e off (k.val*m+i+1)) (mapped a)
      (RoutesV2.targetFlag dst,RoutesV2.targetX dst,RoutesV2.targetY dst) (fun i => mapped (b i))
      (mappedPoint f h a) (targetPoint (RoutesV2.target f) (pathFst h)) (fun i => mappedPoint f h (b i))

attribute [local fun_prop] PolyT.const PolyT.mul PolyT.add PolyT.sub

theorem productFoldsGood {α : Type} [Enc α] {m d e tip off : α → ℕ}
    (hm : PolyT m) (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off) :
    Good fun x => productFolds (m x) (d x) (e x) (tip x) (off x) := by
  have mb {j : α → ℕ} (hj : PolyT j) : PolyT fun x => mapBase (d x) (e x) (off x) (j x) := by
    unfold mapBase; fun_prop (disch := assumption)
  have fb {j : α → ℕ} (hj : PolyT j) : PolyT fun x => foldBase (m x) (d x) (e x) (off x) (j x) := by
    unfold foldBase; fun_prop (disch := assumption)
  have sz : PolyT fun x => groupEdges (m x) (d x) (e x) := by
    unfold groupEdges stepEdges; fun_prop (disch := assumption)
  apply tileGood (PolyT.const 2) sz
  intro k hk
  have base := PolyT.mul hk hm
  exact foldGood (PolyT.sub hm (PolyT.const 1)) hd he ht (fb hk) (mb base) ho
    (fun hj => mb (PolyT.add (PolyT.add base hj) (PolyT.const 1)))

end DetDLP.S8N.MomentStepReuse
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H4.TracksPoly
open private catP from Definitions.Def_DetDLP_S8H4_TracksPoly

namespace AtomRegisters

def affine (a b c d e : ℕ) := a*d+b*e+c
abbrev beforeMux := affine 337 28 150
abbrev fixedWidth := affine 342 28 156
abbrev slotWidth := affine 122 14 46
abbrev seedReg := affine 118 14 45

def localSource (d e i : ℕ) : ℕ :=
  sigNat d e 0 0 (slotWidth d e+2 + (if i < beforeMux d e then i else 3*d+i))

def fixedPart (d e tip off : ℕ) : R :=
  (fixedWidth d e,fun i =>
    let v := localSource d e i
    if v = slotWidth d e then tip else off+v)

def row (d e off : ℕ) (a0 b0 a1 b1 : ℕ → ℕ) (j k : ℕ) : ℕ :=
  if k=0 then off+(3*d+2) else if k<3 then off+seedReg d e+(k-1)*d+j
  else if k=3 then a0 j else if k=4 then b0 j else if k=5 then a1 j else b1 j

def selectPart (d e off : ℕ) (a0 b0 a1 b1 : ℕ → ℕ) : R :=
  (d*7,fun i => row d e off a0 b0 a1 b1 (i/7) (i%7))

def A (d tip start : ℕ) : ℕ → ℕ := pad d tip (start+(3*d+1)+(3*d+1))
def B (d tip start : ℕ) : ℕ → ℕ := pad d tip (start+(3*d+1))

abbrev WordEff {α : Type} [Enc α] (f : α → ℕ → ℕ) :=
  ∀ {i : α → ℕ}, PolyT i → PolyT fun x => f x (i x)

private theorem affinePoly {α : Type} [Enc α] {d e : α → ℕ} (hd : PolyT d) (he : PolyT e)
    (a b c : ℕ) : PolyT fun x => affine a b c (d x) (e x) :=
  PolyT.add (PolyT.add (PolyT.mul (PolyT.const a) hd) (PolyT.mul (PolyT.const b) he)) (PolyT.const c)

end AtomRegisters
open AtomRegisters

def atomTile (d e tip off : ℕ) (a0 b0 a1 b1 : ℕ → ℕ) : R :=
  cat (fixedPart d e tip off) (selectPart d e off a0 b0 a1 b1)

theorem atomTile_length (d e tip off : ℕ) (a0 b0 a1 b1 : ℕ → ℕ) :
    (atomTile d e tip off a0 b0 a1 b1).1 =
      85*(d+1)+7*(4*e+36*d+10)+12*d+1 := by
  change 342*d+28*e+156+d*7 = _
  omega

theorem atomGood {α : Type} [Enc α] {d e tip off : α → ℕ} {a0 b0 a1 b1 : α → ℕ → ℕ}
    (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off)
    (ha0 : WordEff a0) (hb0 : WordEff b0) (ha1 : WordEff a1) (hb1 : WordEff b1) :
    Good fun x => atomTile (d x) (e x) (tip x) (off x) (a0 x) (b0 x) (a1 x) (b1 x) := by
  let C (n : ℕ) : PolyT (fun _ : α => n) := PolyT.const n
  have slot := affinePoly hd he 122 14 46
  apply catP (a:=fun x => fixedPart (d x) (e x) (tip x) (off x))
    (b:=fun x => selectPart (d x) (e x) (off x) (a0 x) (b0 x) (a1 x) (b1 x))
  · refine ⟨affinePoly hd he 342 28 156,fun i hi => ?_⟩
    have src := sigNat_poly hd he (C 0) (C 0) (PolyT.add (PolyT.add slot (C 2))
      (PolyT.ite' (PolyT.decide_lt hi (affinePoly hd he 337 28 150)) hi
        (PolyT.add (PolyT.mul (C 3) hd) hi)))
    exact PolyT.ite' (PolyT.decide_eq src slot) ht (PolyT.add ho src)
  · refine ⟨PolyT.mul hd (C 7),fun i hi => ?_⟩
    have j := PolyT.div hi (C 7)
    have k := PolyT.mod hi (C 7)
    exact PolyT.ite' (PolyT.decide_eq k (C 0)) (PolyT.add ho (PolyT.add (PolyT.mul (C 3) hd) (C 2)))
      (PolyT.ite' (PolyT.decide_lt k (C 3))
        (PolyT.add (PolyT.add (PolyT.add ho (affinePoly hd he 118 14 45)) (PolyT.mul (PolyT.sub k (C 1)) hd)) j)
        (PolyT.ite' (PolyT.decide_eq k (C 3)) (ha0 j) (PolyT.ite' (PolyT.decide_eq k (C 4))
          (hb0 j) (PolyT.ite' (PolyT.decide_eq k (C 5)) (ha1 j) (hb1 j)))))

def pairedAtomTile (d e tip atomOff leftStart rightStart : ℕ) : R :=
  atomTile d e tip atomOff (A d tip leftStart) (B d tip leftStart)
    (A d tip rightStart) (B d tip rightStart)

theorem pairedAtomGood {α : Type} [Enc α] {d e tip off l r : α → ℕ}
    (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off)
    (hl : PolyT l) (hr : PolyT r) :
    Good fun x => pairedAtomTile (d x) (e x) (tip x) (off x) (l x) (r x) := by
  have tri := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  have word {f : α → ℕ} (hf : PolyT f) : WordEff (fun x => pad (d x) (tip x) (f x)) :=
    fun hi => PolyT.ite' (PolyT.decide_lt hi hd) (PolyT.add hf hi) ht
  exact atomGood hd he ht ho (word (PolyT.add (PolyT.add hl tri) tri))
    (word (PolyT.add hl tri)) (word (PolyT.add (PolyT.add hr tri) tri)) (word (PolyT.add hr tri))

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec AtomRegisters
open private edges fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot
open private size_eq from Definitions.Def_DetDLP_S8H4_TracksSpec

private theorem selectTracks {s : Shape} {d e off : ℕ} {a0 b0 a1 b1 : ℕ → ℕ}
    {refs : Fin d → Fin 7 → Ref s} (test)
    (h : ∀ j k, row d e off a0 b0 a1 b1 j.val k.val = (refs j k).source.val) :
    Tracks (selectPart d e off a0 b0 a1 b1) (rows d 7 refs test) :=
  ⟨rfl,fun i => h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩

theorem atomTracks {s : Shape} {d off : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (q : Path (S8M.ECAtomSlot.slotShape d (w4_M5GraphBounds.graph d hd).nE) s)
    (hq : ∀ a, (q a).index.val = off+a.index.val) (a0 b0 a1 b1 : ℕ → ℕ)
    (A0 B0 A1 B1 : Word s)
    (ha0 : ∀ i, a0 i = (A0 i).source.val) (hb0 : ∀ i, b0 i = (B0 i).source.val)
    (ha1 : ∀ i, a1 i = (A1 i).source.val) (hb1 : ∀ i, b1 i = (B1 i).source.val) :
    Tracks (atomTile d (w4_M5GraphBounds.graph d hd).nE s.size off a0 b0 a1 b1)
      (S8M.ECAtomSlot.slotBlock hd p T c A0 B0 A1 B1 q) := by
  apply cat_ok
  · have h := AtomFixedGeometry.tracks hd p T c
    refine ⟨(AtomFixedGeometry.width_eq ..).symm.trans h.1,fun i => ?_⟩
    have hi := lt_of_lt_of_eq i.isLt h.1.symm
    change (if localSource _ _ i.val = slotWidth _ _ then s.size else off+localSource _ _ i.val)
      = (S8M.ECAtomSlot.route q ((fixed hd p T c).name i)).val
    have src : localSource _ _ i.val = _ := AtomFixedGeometry.localSource_eq _ _ _ hi
    have cap : slotWidth _ _ = _ := AtomFixedGeometry.slotWidth_eq d (w4_M5GraphBounds.graph d hd).nE
    rw [src,h.2,AtomFixedGeometry.routeIndex q off hq,cap]
    simp only [S8M.ECAtomSlot.slotShape,size_eq]
  · apply selectTracks
    intro j k
    fin_cases k <;> simp only [row,Fin.val_zero,Fin.val_one,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_succ,Fin.reduceFinMk,Fin.isValue,↓reduceIte,Nat.reduceLT,
      Nat.reduceSub,Nat.zero_mul,Nat.one_mul,Nat.add_zero] <;>
      first | exact ha0 _ | exact hb0 _ | exact ha1 _ | exact hb1 _ | skip
    all_goals simp only [S8H4.Routes.network.coord,S8H4.Routes.network.a6Reg,
      S8H4.Routes.network.b6Reg,GateRoutes.word,HashRows.padded,show 0<d by omega,↓reduceDIte]
    all_goals change _ = (q _).index.val
    all_goals rw [hq]
    all_goals try rw [show seedReg d (w4_M5GraphBounds.graph d hd).nE = _ from
      AtomFixedGeometry.seedReg_eq d (w4_M5GraphBounds.graph d hd).nE]
    all_goals dsimp only [Addr.index,Fin.castAdd,Fin.natAdd,Fin.castLE,Fin.castSucc,RangeRows.ya,
      edges,S8M.ECAtomSlot.slotShape,top,Shape.size,triple]
    all_goals norm_num
    all_goals omega

end DetDLP.S8N.MomentSignal
end


section
set_option autoImplicit false
namespace DetDLP.S8N.SignalGeometry
open Groundwork DetDLP_W1_Queries S8H0 S8H.PortCombinators S8J.CircuitRealizes RegisterMap NamedBlocks
open S8M S8M.PortPoly RoutesV2
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev word (j : Fin 4) (T : ℕ) (η : List Bool) :=
  M89S1.queryWord 2 (encodeCurveInput p E) [countWord j.val, countWord T, η]

theorem prime_word (j : Fin 4) (T : ℕ) (η : List Bool) : S8M.PortPoly.prime (word E j T η) = p := by
  simp [word, M89S1.queryWord, S8M.PortPoly.prime, DetDLP_W1_Queries.second, encodeCurveInput, encodeNatListBin]

abbrev shape (p m : ℕ) (j : Fin 4) :=
  RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)

noncomputable abbrev net {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  joinB (PointGraph.zeroLast (shape p m j).size)
    (RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E) E.b₂.val
      (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η id)

noncomputable abbrev core {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.block (net E hm j T η).core ((shape p m j).size + 1)

noncomputable abbrev wires {m : ℕ} (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.wiring (net E hm j T η).core (net E hm j T η).name

theorem anchor_eq (m d e : ℕ) (j : Fin 4) : PortPoly.anchorCount (copies j) (outputs j) m d e = (RoutesV2.bank j m d e).size + 1 := by
  simp only [PortPoly.anchorCount,RoutesV2.bank,productShape,targetShape,ECSeedBank.ecSeedShape,S8G.SeedAndAtomBank.seedSlot,ECFoldRoutes.foldShape,ECAtomSlot.slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,ECMapRows.mapShape,ECAddRoutes.addShape,ECMapRows.slot,RegisterMap.run,RegisterMap.triple,RegisterMap.mul,GateRoutes.auxShape,Shape.size]; ring

end DetDLP.S8N.SignalGeometry
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.S8N.MomentSignal

open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8M.ECMapRows
open private fstP sndP rwrd sp result remain args4 ranges maskEq gw from Definitions.Def_DetDLP_S8M_ECMapRows
open private manyP from Definitions.Def_DetDLP_S8H4_TracksPoly

private def mapSlotStart (d e off i : ℕ) := off+(1+(triSize d+triSize d))+(runSize d e+auxSize d)*i

private def maskTable (d flag : ℕ) (out z : W) : R :=
  rowTable d 3 (fun i j => if j=0 then flag else if j=1 then out i else z i)

private theorem maskTracks {s : Shape} {d flag : ℕ} {f : Ref s} {a b : W} {A B : Word s}
    (hf : flag = f.source.val) (ha : WordAt a A) (hb : WordAt b B) :
    Tracks (maskTable d flag a b) (maskEq f A B d) := by
  apply rowTracks
  intro i j
  fin_cases j
  · exact hf
  · exact ha _
  · exact hb _

def mapTile (d e tip off flag : ℕ) (x y : W) : R :=
  let a := off+1
  let b := a+triSize d
  let slot := mapSlotStart d e off
  let z := fun i => S8H4.TracksPoly.pad d tip (slot i)
  let pin := fun _ : ℕ => tip
  let checks := cat (cat (checkTile d tip a) (checkTile d tip b))
    (manyR 3 fun i => cat (checkTile d tip (slot i.val)) (checkTile d tip (slot i.val+triSize d)))
  let hashes := manyR 3 fun i => hashTile d e tip (slot i.val) pin
    (if i=2 then y else if i=3 then z 2 else x) (if i=2 then z 1 else pin)
  cat checks (cat hashes (cat (rowTable 1 2 (fun _ j => if j=0 then off else flag))
    (cat (maskTable d flag (S8H4.TracksPoly.pad d tip a) (z 0))
      (maskTable d flag (S8H4.TracksPoly.pad d tip b) (z 3)))))

theorem mapTile_length (d e tip off flag : ℕ) (x y : W) :
    (mapTile d e tip off flag x y).1 = 50*(d+1) + 4*(4*e+36*d+10) + 2 + 6*d := by
  simp only [mapTile,maskTable,checkTile,hashTile,cat,manyR,plusRows,prodR,rowTable]
  omega

theorem mapTracks {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p b2 a1 a3 off flag : ℕ)
    (x y : W) (F : Ref s) (X Y : Word s)
    (f : Path (mapShape d (w4_M5GraphBounds.graph d hd).nE) s)
    (hf : PathAt f off) (hF : flag=F.source.val) (hX : WordAt x X) (hY : WordAt y Y) :
    Tracks (mapTile d (w4_M5GraphBounds.graph d hd).nE s.size off flag x y)
      (mapBlock hd p b2 a1 a3 F X Y f) := by
  let e := (w4_M5GraphBounds.graph d hd).nE
  have outX : PathAt (fstP (sndP (fstP f))) (off+1) := pathFst (pathSnd (pathFst hf))
  have outY : PathAt (sndP (sndP (fstP f))) (off+1+triSize d) := by
    rw [← triSize_eq]
    exact pathSnd (pathSnd (pathFst hf))
  have slotAt (i : Fin 4) : PathAt (sp f i) (mapSlotStart d e off i.val) := by
    have h : PathAt (sp f i)
        (off+(1+((triple d).size+(triple d).size))+((run d e).size+(auxShape d).size)*i.val) :=
      pathVec (pathSnd hf) i
    simpa only [triSize_eq,runSize_eq,auxSize_eq,mapSlotStart] using h
  have res (i : Fin 4) := pathFst (pathFst (slotAt i))
  have remn (i : Fin 4) : PathAt (remain (sp f i)) (mapSlotStart d e off i.val+triSize d) := by
    simpa only [triSize_eq] using pathFst (pathFst (pathSnd (pathFst (slotAt i))))
  have wordRes (i : Fin 4) : WordAt (S8H4.TracksPoly.pad d s.size (mapSlotStart d e off i.val))
      (rwrd (result (sp f i))) := pathWord _ _ (pathFst (res i))
  have pin (n : ℕ) : WordAt (fun _ => s.size) (pub n (s:=s)) := fun _ => rfl
  unfold mapTile mapBlock ranges
  refine cat_ok (cat_ok (cat_ok (checkTracks p _ _ outX) (checkTracks p _ _ outY))
    (many_ok _ _ _ fun i => cat_ok (checkTracks p _ _ (res i)) (checkTracks p _ _ (remn i))))
    (cat_ok (many_ok _ _ _ fun i => ?_) (cat_ok ?_ (cat_ok ?_ ?_)))
  · apply hashTracks hd p _ _ (slotAt i)
    all_goals fin_cases i <;> first | exact pin _ | exact hX | exact hY | exact wordRes 1 | exact wordRes 2
  · apply rowTracks
    intro i j
    fin_cases j
    · change off = (f (.fst (.fst .bit))).index.val
      rw [hf]
      rfl
    · exact hF
  · exact maskTracks hF (pathWord _ _ (pathFst outX)) (wordRes 0)
  · exact maskTracks hF (pathWord _ _ (pathFst outY)) (wordRes 3)

attribute [local fun_prop] PolyT.const PolyT.mul PolyT.add PolyT.ite' PolyT.decide_eq
  P2M_Groundwork_PolyT_ite__226169acf219

private theorem maskGood {α : Type} [Enc α] {d flag : α → ℕ} {a b : α → W}
    (hd : PolyT d) (hf : PolyT flag) (ha : WordCode a) (hb : WordCode b) :
    Good fun z => maskTable (d z) (flag z) (a z) (b z) := by
  apply rowGood hd (PolyT.const 3)
  intro i j hi hj
  exact PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) hf
    (PolyT.ite' (PolyT.decide_eq hj (PolyT.const 1)) (ha hi) (hb hi))

set_option maxHeartbeats 650000 in
theorem mapGood {α : Type} [Enc α] {d e tip off flag : α → ℕ} {x y : α → W}
    (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off) (hf : PolyT flag)
    (hx : WordCode x) (hy : WordCode y) :
    Good fun z => mapTile (d z) (e z) (tip z) (off z) (flag z) (x z) (y z) := by
  have ht' : PolyT fun z => triSize (d z) := by unfold triSize; fun_prop (disch := assumption)
  have hs (i : ℕ) : PolyT fun z => mapSlotStart (d z) (e z) (off z) i := by
    unfold mapSlotStart runSize auxSize
    fun_prop (disch := assumption)
  have ha := PolyT.add ho (PolyT.const 1)
  have hb := PolyT.add ha ht'
  unfold mapTile
  refine catGood (catGood (catGood (checkGood hd ht ha) (checkGood hd ht hb))
    (manyP 3 _ fun i => catGood (checkGood hd ht (hs i.val)) (checkGood hd ht (PolyT.add (hs i.val) ht'))))
    (catGood (manyP 3 _ fun i => ?_) (catGood ?_ (catGood (maskGood hd hf (wordGood hd ht ha) (wordGood hd ht (hs 0)))
      (maskGood hd hf (wordGood hd ht hb) (wordGood hd ht (hs 3))))))
  · apply hashGood hd he ht (hs i.val) (fun _ => ht)
    all_goals fin_cases i <;> first | exact hx | exact hy | exact wordGood hd ht (hs 2) | exact wordGood hd ht (hs 1) | exact fun _ => ht
  · apply rowGood (PolyT.const 1) (PolyT.const 2)
    intro i j _ hj
    exact PolyT.ite' (PolyT.decide_eq hj (PolyT.const 0)) ho hf

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8M.ECFoldRoutes ECAddRoutes

abbrev PointName := ℕ × W × W
abbrev PointRef (s : Shape) := Ref s × Word s × Word s
abbrev PointAt {s : Shape} (P : PointName) (r : PointRef s) :=
  P.1 = r.1.source.val ∧ WordAt P.2.1 r.2.1 ∧ WordAt P.2.2 r.2.2
abbrev PointGood {α : Type} [Enc α] (P : α → PointName) :=
  PolyT (fun x => (P x).1) ∧ WordCode (fun x => (P x).2.1) ∧ WordCode (fun x => (P x).2.2)

def pointName (d tip off : ℕ) : PointName :=
  (off,S8H4.TracksPoly.pad d tip (off+1),S8H4.TracksPoly.pad d tip (off+1+triSize d))

def addShapeSize (d e : ℕ) := (1+4*triSize d)+((2+d)+15*(runSize d e+auxSize d))
theorem addShapeSize_eq (d e : ℕ) : (addShape d e).size = addShapeSize d e := by
  simp only [addShapeSize,addShape,Shape.size,S8M.ECMapRows.slot,triSize_eq,runSize_eq,auxSize_eq,Nat.mul_one]

def stepEdges (d e : ℕ) := 170*(d+1)+15*(4*e+36*d+10)+31*d+5

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H4.TracksPoly
attribute [local fun_prop] PolyT.const PolyT.mul PolyT.add

theorem pointGood {α : Type} [Enc α] {d tip off : α → ℕ}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) : PointGood fun z => pointName (d z) (tip z) (off z) := by
  have tr := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  have base := PolyT.add ho (PolyT.const 1)
  exact ⟨ho,wordGood hd ht base,wordGood hd ht (PolyT.add base tr)⟩

theorem addShapeGood {α : Type} [Enc α] {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) :
    PolyT fun z => addShapeSize (d z) (e z) := by
  unfold addShapeSize triSize auxSize runSize
  fun_prop (disch := assumption)

end DetDLP.S8N.MomentSignal
end


section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires RangeRows HashRows
open S8H4.TracksPoly S8G.SeedAndAtomBank

def seedSlotSize (d : ℕ) := 8*d+3
def seedPairOff (d off i : ℕ) := off+(seedSlotSize d+seedSlotSize d)*i
def seedOff (d off i : ℕ) (side : Bool) :=
  if side then seedPairOff d off i+seedSlotSize d else seedPairOff d off i
def seedAWord (d tip off i : ℕ) (side : Bool) : W :=
  S8H4.TracksPoly.pad d tip (seedOff d off i side+(3*d+1)+(3*d+1))
def seedBWord (d tip off i : ℕ) (side : Bool) : W :=
  S8H4.TracksPoly.pad d tip (seedOff d off i side+(3*d+1))

theorem seedSlotSize_eq (d : ℕ) : (seedSlot d).size = seedSlotSize d := by
  simp only [seedSlot,triple,Shape.size,seedSlotSize]
  omega

theorem seedPathAt {s : Shape} {m d off : ℕ} {q : Path (ECSeedBank.ecSeedShape m d) s}
    (hq : PathAt q off) (i : Fin m) (side : Bool) :
    PathAt (RoutesV2.seedSlotPath q i side) (seedOff d off i.val side) := by
  have hs := @pathVec m (.pair (seedSlot d) (seedSlot d)) s q off hq i
  cases side
  · change PathAt (fun a => q (.vec i (.fst a))) _
    simpa only [seedOff,seedPairOff,Shape.size,seedSlotSize_eq,
      Bool.false_eq_true,if_false] using pathFst hs
  · change PathAt (fun a => q (.vec i (.snd a))) _
    simpa only [seedOff,seedPairOff,Shape.size,seedSlotSize_eq,if_true] using pathSnd hs

theorem seedAWordAt {s : Shape} {m d off : ℕ} {q : Path (ECSeedBank.ecSeedShape m d) s}
    (hq : PathAt q off) (i : Fin m) (side : Bool) :
    WordAt (seedAWord d s.size off i.val side)
      (ECSeedBank.ecSeedA (RoutesV2.seedSlotPath q i side)) := by
  unfold seedAWord ECSeedBank.ecSeedA S8G.SeedAndAtomBank.seedA
  apply pathWord
  have hs := seedPathAt hq i side
  have hlen : (triple d).size = 3*d+1 := by simp only [triple,Shape.size]; omega
  simpa only [hlen] using pathFst (pathSnd (pathSnd hs))

theorem seedBWordAt {s : Shape} {m d off : ℕ} {q : Path (ECSeedBank.ecSeedShape m d) s}
    (hq : PathAt q off) (i : Fin m) (side : Bool) :
    WordAt (seedBWord d s.size off i.val side)
      (ECSeedBank.ecSeedB (RoutesV2.seedSlotPath q i side)) := by
  unfold seedBWord ECSeedBank.ecSeedB S8G.SeedAndAtomBank.seedB
  apply pathWord
  have hs := seedPathAt hq i side
  have hlen : (triple d).size = 3*d+1 := by simp only [triple,Shape.size]; omega
  simpa only [hlen] using pathFst (pathFst (pathSnd hs))

theorem seedOffPoly {α : Type} [Enc α] {d off i : α → ℕ} {side : α → Bool}
    (hd : PolyT d) (ho : PolyT off) (hi : PolyT i) (hs : PolyT side) :
    PolyT fun x => seedOff (d x) (off x) (i x) (side x) := by
  have k := PolyT.add (PolyT.mul (PolyT.const 8) hd) (PolyT.const 3)
  have p := PolyT.add ho (PolyT.mul (PolyT.add k k) hi)
  exact PolyT.ite' (by simpa using hs) (PolyT.add p k) p

theorem seedAWordCode {α : Type} [Enc α] {d tip off i : α → ℕ} {side : α → Bool}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) (hi : PolyT i) (hs : PolyT side) :
    WordCode fun x => seedAWord (d x) (tip x) (off x) (i x) (side x) := by
  have t := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  intro k hk
  exact wordGood hd ht (PolyT.add (PolyT.add (seedOffPoly hd ho hi hs) t) t) hk

theorem seedBWordCode {α : Type} [Enc α] {d tip off i : α → ℕ} {side : α → Bool}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) (hi : PolyT i) (hs : PolyT side) :
    WordCode fun x => seedBWord (d x) (tip x) (off x) (i x) (side x) := by
  intro k hk
  exact wordGood hd ht (PolyT.add (seedOffPoly hd ho hi hs)
    (PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1))) hk

def ecPrefixSignal (b m d tip off i : ℕ) : ℕ :=
  if i < m*4*b then
    let k := i / b
    let side := decide (2 ≤ k % 4)
    let bit := b-(i%b+1)
    if k%4%2=0 then seedAWord d tip off (k/4) side bit
    else seedBWord d tip off (k/4) side bit
  else tip

theorem ecPrefixSignalAt {s : Shape} {m d off : ℕ} (p : ℕ)
    {q : Path (ECSeedBank.ecSeedShape m d) s} (hq : PathAt q off) (i : ℕ) :
    ecPrefixSignal (bitLen p) m d s.size off i = (RoutesV2.ecPrefixBit p q i).source.val := by
  unfold ecPrefixSignal RoutesV2.ecPrefixBit
  split <;> rename_i h
  · let v : Fin (m*4) × Fin (bitLen p) := finProdFinEquiv.symm ⟨i,h⟩
    let w : Fin m × Fin 4 := finProdFinEquiv.symm v.1
    have a := seedAWordAt hq w.1 (decide (2 ≤ w.2.val)) v.2.rev.val
    have b := seedBWordAt hq w.1 (decide (2 ≤ w.2.val)) v.2.rev.val
    change (if w.2.val%2=0 then _ else _) =
      ((if w.2.val%2=0 then ECSeedBank.ecSeedA _ else ECSeedBank.ecSeedB _)
        v.2.rev.val).source.val
    split <;> first | exact a | exact b
  · rfl

theorem ecPrefixSignalPoly {α : Type} [Enc α] {b m d tip off i : α → ℕ}
    (hb : PolyT b) (hm : PolyT m) (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off)
    (hi : PolyT i) :
    PolyT fun x => ecPrefixSignal (b x) (m x) (d x) (tip x) (off x) (i x) := by
  have four := PolyT.const (α:=α) 4
  have two := PolyT.const (α:=α) 2
  have k := PolyT.div hi hb
  have r := PolyT.mod k four
  have side := PolyT.decide_le two r
  have j := PolyT.div k four
  have idx := PolyT.sub hb (PolyT.add (PolyT.mod hi hb) (PolyT.const 1))
  exact PolyT.ite' (PolyT.decide_lt hi (PolyT.mul (PolyT.mul hm four) hb))
    (PolyT.ite' (PolyT.decide_eq (PolyT.mod r two) (PolyT.const 0))
      (seedAWordCode hd ht ho j side idx) (seedBWordCode hd ht ho j side idx)) ht

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8G.SeedAndAtomBank
open private plusP from Definitions.Def_DetDLP_S8H4_TracksPoly

def seedSlotTile (d tip off : ℕ) : R :=
  let t := 3*d+1
  cat (checkTile d tip off) (cat (checkTile d tip (off+t))
    (plusRows (d+1) (S8H4.TracksPoly.pad d tip off) (fun _ => tip)
      (S8H4.TracksPoly.pad d tip (off+t+t)) (off+t+t+d+·)))

theorem seedSlotTracks {s : Shape} {d off : ℕ} (p : ℕ)
    (q : Path (seedSlot d) s) (hq : PathAt q off) :
    Tracks (seedSlotTile d s.size off) (ECSeedBank.ecSeedSlotBlock p q) := by
  have t : (triple d).size = 3*d+1 := triSize_eq d
  have h₁ := pathFst hq
  have h₂ := pathFst (pathSnd hq)
  rw [t] at h₂
  refine cat_ok (checkTracks (p-1) off _ h₁) (cat_ok (checkTracks p _ _ h₂) ?_)
  apply plus_ok
  intro j
  refine ⟨?_, rfl, ?_, ?_⟩
  · exact pathWord _ _ (pathFst h₁) j.val
  · have w := pathWord _ _ (pathFst (pathSnd (pathSnd hq)))
    simpa only [t,S8G.SeedAndAtomBank.seedA] using w j.val
  · change _ = (q _).index.val
    rw [hq]
    change _ = off+((triple d).size+((triple d).size+(d+j.val)))
    rw [t]
    omega

theorem seedSlotGood {α : Type} [Enc α] {d tip off : α → ℕ}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) :
    Good fun x => seedSlotTile (d x) (tip x) (off x) := by
  have t := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  have t1 := PolyT.add ho t
  have t2 := PolyT.add t1 t
  refine catGood (checkGood hd ht ho) (catGood (checkGood hd ht t1) ?_)
  exact @plusP α _ (fun x => d x+1) (fun x => S8H4.TracksPoly.pad (d x) (tip x) (off x))
    (fun x _ => tip x)
    (fun x => S8H4.TracksPoly.pad (d x) (tip x) (off x+(3*d x+1)+(3*d x+1)))
    (fun x i => off x+(3*d x+1)+(3*d x+1)+d x+i)
    (PolyT.add hd (PolyT.const 1)) (wordGood hd ht ho)
    (fun _ => ht) (wordGood hd ht t2) (fun hi => PolyT.add (PolyT.add t2 hd) hi)

def seedTile (b m d tip off prefixLen : ℕ) : R :=
  cat (tileTable m (6*((d+1)*5)) fun i =>
    cat (seedSlotTile d tip (seedOff d off i false))
      (seedSlotTile d tip (seedOff d off i true)))
    (rowTable prefixLen 1 (fun i _ => ecPrefixSignal b m d tip off i))

theorem seedTracks {s : Shape} {d m off : ℕ} (p : ℕ) (η : List Bool)
    (q : Path (ECSeedBank.ecSeedShape m d) s) (hq : PathAt q off) :
    Tracks (seedTile (bitLen p) m d s.size off η.length) (RoutesV2.ecSeedBlockV2 p m η q) := by
  apply cat_ok
  · apply tileTracks
    · intro i
      simp only [cat,seedSlotTile,checkTile,plusRows]
      omega
    · intro i
      exact cat_ok (seedSlotTracks p _ (seedPathAt hq i false))
        (seedSlotTracks p _ (seedPathAt hq i true))
  · apply rowTracks
    intro i _
    exact ecPrefixSignalAt p hq i.val

theorem seedGood {α : Type} [Enc α] {b m d tip off len : α → ℕ}
    (hb : PolyT b) (hm : PolyT m) (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off)
    (hl : PolyT len) : Good fun x => seedTile (b x) (m x) (d x) (tip x) (off x) (len x) := by
  apply catGood
  · apply tileGood hm (PolyT.mul (PolyT.const 6)
      (PolyT.mul (PolyT.add hd (PolyT.const 1)) (PolyT.const 5)))
    intro i hi
    exact catGood (seedSlotGood hd ht (seedOffPoly hd ho hi (PolyT.const false)))
      (seedSlotGood hd ht (seedOffPoly hd ho hi (PolyT.const true)))
  · apply rowGood hl (PolyT.const 1)
    intro i k hi _
    exact ecPrefixSignalPoly hb hm hd ht ho hi

end DetDLP.S8N.MomentSignal
end


section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8M.ECMapRows S8M.ECFoldRoutes
open private firstIndex_lt from Definitions.Def_DetDLP_S8N_Routes_v3

def targetSize (d : ℕ) := 1+(triSize d+triSize d)
def mapSize (d e : ℕ) := targetSize d+4*(runSize d e+auxSize d)
def mapEdges (d e : ℕ) := 50*(d+1)+4*(4*e+36*d+10)+2+6*d
def foldEdges (n d e : ℕ) := 2+4*d+n*stepEdges d e

theorem targetSize_eq (d : ℕ) : (RoutesV2.targetShape d).size = targetSize d := by
  simp only [RoutesV2.targetShape,targetSize,Shape.size,triSize_eq]
theorem mapSize_eq (d e : ℕ) : (mapShape d e).size = mapSize d e := by
  simp only [mapShape,targetSize,mapSize,S8M.ECMapRows.slot,Shape.size,triSize_eq,runSize_eq,auxSize_eq]

abbrev targetRefs {d : ℕ} {s : Shape} (f : Path (RoutesV2.targetShape d) s) : PointRef s :=
  (RoutesV2.targetFlag f,RoutesV2.targetX f,RoutesV2.targetY f)
abbrev mapRefs {d e : ℕ} {s : Shape} (f : Path (mapShape d e) s) : PointRef s :=
  (RoutesV2.mapFlag f,RoutesV2.mapX f,RoutesV2.mapY f)

theorem targetPoints {d off : ℕ} {s : Shape} (f : Path (RoutesV2.targetShape d) s) (h : PathAt f off) :
    PointAt (pointName d s.size off) (targetRefs f) := by
  refine ⟨?_,pathWord _ _ (pathFst (pathFst (pathSnd h))),?_⟩
  · change off = (f (.fst .bit)).index.val
    simpa only [Addr.index,Fin.val_castAdd,Fin.val_zero,Nat.add_zero] using (h (.fst .bit)).symm
  · change WordAt (S8H4.TracksPoly.pad d s.size (off+1+triSize d))
      (word fun a : Addr (.word d) => f (.snd (.snd (.fst a))))
    simpa only [Shape.size,triSize_eq] using pathWord _ _ (pathFst (pathSnd (pathSnd h)))

def targetTile (d tip off : ℕ) : R :=
  let P := pointName d tip off
  cat (checkTile d tip (off+1)) <| cat (checkTile d tip (off+1+triSize d))
    (vectorRows d ![fun _ => P.1,P.2.1,P.2.2])

theorem targetTracks {d : ℕ} {s : Shape} (p off : ℕ) (f : Path (RoutesV2.targetShape d) s) (hf : PathAt f off) :
    Tracks (targetTile d s.size off) (RoutesV2.targetBlock p f) := by
  have h := targetPoints f hf
  have y : PathAt (fun a => f (.snd (.snd a))) (off+1+triSize d) := by
    simpa only [Shape.size,triSize_eq] using pathSnd (pathSnd hf)
  apply cat_ok (checkTracks p _ _ (pathFst (pathSnd hf))) (cat_ok (checkTracks p _ _ y) ?_)
  apply vectorTracks
  intro j i
  fin_cases j <;> first | exact h.1 | exact h.2.1 _ | exact h.2.2 _

def mapStart (d e off k : ℕ) := off+targetSize d+mapSize d e*k

def productTile (m d e tip off : ℕ) (A : ℕ → PointName) : R :=
  let mOff := mapStart d e off
  cat (targetTile d tip off) <| cat
    (tileTable (2*m) (mapEdges d e) fun k =>
      mapTile d e tip (mOff k) (A k).1 (A k).2.1 (A k).2.2) <|
    MomentStepReuse.productFolds m d e tip off

theorem productTile_length (m d e tip off : ℕ) (A : ℕ → PointName) :
    (productTile m d e tip off A).1 =
      (10*(d+1)+3*d) + ((2*m)*mapEdges d e+2*foldEdges (m-1) d e) := by
  change ((d+1)*5+((d+1)*5+d*3))+((2*m)*mapEdges d e+(MomentStepReuse.productFolds m d e tip off).1) = _
  rw [MomentStepReuse.productFoldsLength]
  unfold foldEdges stepEdges MomentStepReuse.stepEdges
  omega

theorem productTracks {m d : ℕ} {s : Shape} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (p bTwo a1 a3 neg three c4 off : ℕ)
    (f : Path (RoutesV2.productShape m d (w4_M5GraphBounds.graph d hd).nE) s) (hf : PathAt f off)
    (A : ℕ → PointName) (B : Fin (2*m) → PointRef s) (hi : ∀ k : Fin (2*m), PointAt (A k.val) (B k)) :
    let e := (w4_M5GraphBounds.graph d hd).nE
    let t := targetRefs (RoutesV2.target f)
    let M := fun k => mapRefs (RoutesV2.mapPath f k)
    let first (k : Fin 2) : Fin (2*m) := ⟨k.val*m,firstIndex_lt hm k⟩
    Tracks (productTile m d e s.size off A)
      (joinB (RoutesV2.targetBlock p (RoutesV2.target f)) (joinB
        (S8G.SeedAndAtomBank.allRows (2*m) fun k =>
          mapBlock hd p bTwo a1 a3 (B k).1 (B k).2.1 (B k).2.2 (RoutesV2.mapPath f k))
        (S8G.SeedAndAtomBank.allRows 2 fun k => foldBlock hd p neg three c4
          (M (first k)).1 (M (first k)).2.1 (M (first k)).2.2
          (RoutesV2.foldFlag hm f k) (RoutesV2.foldX hm f k) (RoutesV2.foldY hm f k)
          t.1 t.2.1 t.2.2 (RoutesV2.foldPath f k)))) := by
  let e := (w4_M5GraphBounds.graph d hd).nE
  have mp (k : Fin (2*m)) : PathAt (RoutesV2.mapPath f k) (mapStart d e off k.val) := by
    change PathAt (fun a => f (.snd (.fst (.vec k a)))) _
    simpa only [mapStart,targetSize_eq,mapSize_eq] using pathVec (pathFst (pathSnd hf)) k
  apply cat_ok (targetTracks p off _ (pathFst hf))
  apply cat_ok
  · apply tileTracks
    · exact fun k => mapTile_length ..
    · intro k
      exact mapTracks hd p bTwo a1 a3 _ _ _ _ _ _ _ _ (mp k) (hi k).1 (hi k).2.1 (hi k).2.2
  · exact MomentStepReuse.productFoldsTracks hm hd p neg three c4 f hf

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H4.TracksPoly
attribute [local fun_prop] PolyT.mul PolyT.add PolyT.sub PolyT.const

theorem targetSizeGood {α : Type} [Enc α] {d : α → ℕ} (hd : PolyT d) :
    PolyT fun z => targetSize (d z) := by
  unfold targetSize triSize
  fun_prop (disch := assumption)

theorem mapSizeGood {α : Type} [Enc α] {d e : α → ℕ} (hd : PolyT d) (he : PolyT e) :
    PolyT fun z => mapSize (d z) (e z) := by
  have h := targetSizeGood hd
  unfold mapSize runSize auxSize
  fun_prop (disch := assumption)

theorem targetGood {α : Type} [Enc α] {d tip off : α → ℕ}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) : Good fun z => targetTile (d z) (tip z) (off z) := by
  let t := pointGood hd ht ho
  have tr := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
  have a := PolyT.add ho (PolyT.const 1)
  apply catGood (checkGood hd ht a) (catGood (checkGood hd ht (PolyT.add a tr)) (vectorGood hd ?_))
  intro j
  fin_cases j <;> first | exact fun _ => t.1 | exact t.2.1 | exact t.2.2

theorem productGood {α : Type} [Enc α] {m d e tip off : α → ℕ} {A : α → ℕ → PointName}
    (hm : PolyT m) (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off)
    (ha : ∀ {k : α → ℕ}, PolyT k → PointGood fun z => A z (k z)) :
    Good fun z => productTile (m z) (d z) (e z) (tip z) (off z) (A z) := by
  have ms := mapSizeGood hd he
  have ts := targetSizeGood hd
  have m2 := PolyT.mul (PolyT.const 2) hm
  have first := PolyT.add ho ts
  have mo {k : α → ℕ} (hk : PolyT k) : PolyT fun z => mapStart (d z) (e z) (off z) (k z) :=
    PolyT.add first (PolyT.mul ms hk)
  have me : PolyT fun z => mapEdges (d z) (e z) := by unfold mapEdges; fun_prop (disch := assumption)
  unfold productTile
  apply catGood (targetGood hd ht ho) (catGood (tileGood m2 me ?_) (MomentStepReuse.productFoldsGood hm hd he ht ho))
  intro k hk
  have a := ha hk
  exact mapGood hd he ht (mo hk) a.1 a.2.1 a.2.2

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8M.ECAtomSlot S8N.ECSeedBank
open S8M.ECFoldRoutes S8M.ECMapRows

def atomSize (d e : ℕ) := 122*d+14*e+46
def atomEdges (d e : ℕ) := 85*(d+1)+7*(4*e+36*d+10)+12*d+1
def seedSize (m d : ℕ) := m*(16*d+6)
def productSize' (m d e : ℕ) := targetSize d + ((2*m)*mapSize d e + 2*((m-1)*addShapeSize d e))
def productEdges (m d e : ℕ) := (10*(d+1)+3*d) + ((2*m)*mapEdges d e+2*foldEdges (m-1) d e)

theorem atomSize_eq (d e : ℕ) : (slotShape d e).size = atomSize d e := by
  simp only [slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,Shape.size,runSize_eq,triSize_eq,
    runSize,triSize,atomSize]
  omega
theorem seedSize_eq (m d : ℕ) : (ecSeedShape m d).size = seedSize m d := by
  simp only [ecSeedShape,Shape.size,seedSlotSize_eq,seedSlotSize,seedSize]
  ring
theorem productSize_eq (m d e : ℕ) : (RoutesV2.productShape m d e).size = productSize' m d e := by
  simp only [RoutesV2.productShape,foldShape,Shape.size,targetSize_eq,mapSize_eq,addShapeSize_eq,productSize']

def atomStart (off m d e k i : ℕ) := off+seedSize m d+(m*atomSize d e)*k+atomSize d e*i
def productStart (off m d e c t : ℕ) := off+seedSize m d+c*(m*atomSize d e)+productSize' m d e*t

def networkTile (b m d e c o tip off len : ℕ) : R :=
  let F := fun k i => atomStart off m d e k i
  let P := fun j => pointName d tip (F (j/m) (j%m))
  cat (seedTile b m d tip off len) <| cat
    (tileTable c (m*atomEdges d e) fun k => tileTable m (atomEdges d e) fun i =>
      atomTile d e tip (F k i) (seedAWord d tip off i false) (seedBWord d tip off i false)
        (seedAWord d tip off i true) (seedBWord d tip off i true))
    (tileTable o (productEdges m d e) fun t => productTile m d e tip (productStart off m d e c t) P)

private theorem atomPoints {d e off : ℕ} {s : Shape} (f : Path (slotShape d e) s) (h : PathAt f off) :
    PointAt (pointName d s.size off) (RoutesV2.pointFlag f,RoutesV2.pointX f,RoutesV2.pointY f) :=
  targetPoints (fun a => f (.fst (.fst a))) (pathFst (pathFst h))

set_option maxHeartbeats 800000 in
theorem networkTracks {m d off : ℕ} {s : Shape} (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ)
    (c : Coeff) (b2 neg three c4 : ℕ) (j : Fin 4) (η : List Bool)
    (f : Path (RoutesV2.bank j m d (w4_M5GraphBounds.graph d hd).nE) s) (hf : PathAt f off) :
    let e := (w4_M5GraphBounds.graph d hd).nE
    Tracks (networkTile (bitLen p) m d e (RoutesV2.copies j) (RoutesV2.outputs j) s.size off η.length)
      (RoutesV2.network hd hm p T c b2 neg three c4 j η f) := by
  let e := (w4_M5GraphBounds.graph d hd).nE
  have se : PathAt (RoutesV2.seeds f) off := pathFst hf
  have atA (k : Fin (RoutesV2.copies j)) (i : Fin m) :
      PathAt (RoutesV2.atom f k i) (atomStart off m d e k.val i.val) := by
    change PathAt (fun a => f (.snd (.fst (.vec k (.vec i a))))) (atomStart off m d e k.val i.val)
    simpa only [e,atomStart,Shape.size,seedSize_eq,atomSize_eq] using
      pathVec (pathVec (pathFst (pathSnd hf)) k) i
  have atP (t : Fin (RoutesV2.outputs j)) :
      PathAt (RoutesV2.product f t) (productStart off m d e (RoutesV2.copies j) t.val) := by
    change PathAt (fun a => f (.snd (.snd (.vec t a)))) (productStart off m d e (RoutesV2.copies j) t.val)
    simpa only [e,productStart,Shape.size,seedSize_eq,atomSize_eq,productSize_eq] using
      pathVec (pathSnd (pathSnd hf)) t
  unfold networkTile RoutesV2.network
  apply cat_ok (seedTracks p η _ se)
  apply cat_ok
  · apply tileTracks
    · exact fun _ => rfl
    · intro k
      apply tileTracks
      · exact fun _ => atomTile_length ..
      · intro i
        exact atomTracks hd p T c _ (atA k i) _ _ _ _ _ _ _ _
          (seedAWordAt se i false) (seedBWordAt se i false) (seedAWordAt se i true) (seedBWordAt se i true)
  · apply tileTracks
    · exact fun _ => productTile_length ..
    · intro t
      let cout := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
      let path (k : Fin (2*m)) := RoutesV2.atom f (RoutesV2.copyIdx cout k) (RoutesV2.slotIdx hm k)
      let A := fun k : ℕ => pointName d s.size (atomStart off m d e (k/m) (k%m))
      let B := fun k : Fin (2*m) =>
        (RoutesV2.pointFlag (path k),RoutesV2.pointX (path k),RoutesV2.pointY (path k))
      have H (k : Fin (2*m)) : PointAt (A k.val) (B k) :=
        atomPoints _ (atA (RoutesV2.copyIdx cout k) (RoutesV2.slotIdx hm k))
      exact productTracks hd hm p b2 c.a1 c.a3 neg three c4 _ _ (atP t) A B H

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes S8H4.TracksPoly S8H4.TracksRowsSpec

attribute [local fun_prop] PolyT.mul PolyT.add PolyT.sub PolyT.div PolyT.mod PolyT.const
  targetSizeGood mapSizeGood addShapeGood

theorem networkGood {α : Type} [Enc α] {b m d e c o tip off len : α → ℕ}
    (hb : PolyT b) (hm : PolyT m) (hd : PolyT d) (he : PolyT e) (hc : PolyT c) (ho : PolyT o)
    (ht : PolyT tip) (hf : PolyT off) (hl : PolyT len) :
    Good fun z => networkTile (b z) (m z) (d z) (e z) (c z) (o z) (tip z) (off z) (len z) := by
  have ae : PolyT fun z => atomEdges (d z) (e z) := by
    unfold atomEdges; fun_prop (disch := assumption)
  have pe : PolyT fun z => productEdges (m z) (d z) (e z) := by
    unfold productEdges mapEdges foldEdges stepEdges; fun_prop (disch := assumption)
  have atom (k i : α → ℕ) (hk : PolyT k) (hi : PolyT i) :
      PolyT fun z => atomStart (off z) (m z) (d z) (e z) (k z) (i z) := by
    unfold atomStart atomSize seedSize; fun_prop (disch := assumption)
  have prod (t : α → ℕ) (h : PolyT t) :
      PolyT fun z => productStart (off z) (m z) (d z) (e z) (c z) (t z) := by
    unfold productStart productSize' atomSize seedSize; fun_prop (disch := assumption)
  unfold networkTile
  apply catGood (seedGood hb hm hd ht hf hl) (catGood (tileGood hc (PolyT.mul hm ae) ?_) (tileGood ho pe ?_))
  · intro k hk
    apply tileGood hm ae
    intro i hi
    exact atomGood hd he ht (atom k i hk hi)
      (seedAWordCode hd ht hf hi (PolyT.const false)) (seedBWordCode hd ht hf hi (PolyT.const false))
      (seedAWordCode hd ht hf hi (PolyT.const true)) (seedBWordCode hd ht hf hi (PolyT.const true))
  · intro t tP
    apply productGood hm hd he ht (prod t tP)
    intro i hi
    exact pointGood hd ht (atom _ _ (PolyT.div hi hm) (PolyT.mod hi hm))

def anchoredTable (b m d e c o len : ℕ) : R :=
  let n := PortPoly.anchorCount c o m d e
  let tip := n-1
  cat (n,id) (cat (1,fun _ => tip) (networkTile b m d e c o tip 0 len))

def wordTable (w : List Bool) : R :=
  let b := S8G.FpMoment.Code.width (S8M.PortPoly.prime w)
  let d := b+1
  let e := S8H.PointAddresses.wires d
  let m := S8G.FpMoment.Code.slots b
  let j := PortPoly.idx w
  anchoredTable b m d e (min j 2) (if j=3 then 1 else 0) (PortPoly.prefixBits w).length

/-- Numeric signal name of a gate incidence on an encoded query. -/
def signal (w : List Bool) (i : ℕ) : ℕ := (wordTable w).2 i

private theorem anchorPoly {α : Type} [Enc α] {c o m d e : α → ℕ}
    (hc : PolyT c) (ho : PolyT o) (hm : PolyT m) (hd : PolyT d) (he : PolyT e) :
    PolyT fun x => PortPoly.anchorCount (c x) (o x) (m x) (d x) (e x) := by
  unfold PortPoly.anchorCount; fun_prop (disch := assumption)

theorem anchoredGood {α : Type} [Enc α] {b m d e c o len : α → ℕ}
    (hb : PolyT b) (hm : PolyT m) (hd : PolyT d) (he : PolyT e) (hc : PolyT c) (ho : PolyT o) (hl : PolyT len) :
    Good fun z => anchoredTable (b z) (m z) (d z) (e z) (c z) (o z) (len z) := by
  have a := anchorPoly hc ho hm hd he
  have tip := PolyT.sub a (PolyT.const 1)
  have h := networkGood hb hm hd he hc ho tip (PolyT.const 0) hl
  exact catGood ⟨a,fun _ hi => hi⟩ (catGood ⟨PolyT.const 1,fun _ _ => tip⟩ h)

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal
open S8H0 RegisterMap GateRoutes NamedBlocks S8H4.TracksPoly S8H4.TracksRowsSpec

private theorem anchoredName {s : Shape} (B : NamedBlocks.B (s.size+1)) (f : R) (h : Tracks f B) :
    let N := joinB (PointGraph.zeroLast s.size) B
    ∀ i : Fin (AnchoredLayout.block N.core (s.size+1)).A.ne,
      (cat (s.size+1,id) (cat (1,fun _ => s.size) f)).2 i.val =
      (AnchoredLayout.signal N.core N.name i).val := by
  let anc : NamedBlocks.B (s.size+1) := ⟨⟨AnchoredLayout.anchors _,fun _ _ => true⟩,id⟩
  have hz : Tracks ((1,fun _ => s.size) : R) (PointGraph.zeroLast s.size) := ⟨rfl,fun _ => rfl⟩
  have a : Tracks ((s.size+1,id) : R) anc := ⟨rfl,fun _ => rfl⟩
  exact (cat_ok a (cat_ok hz h)).2

private theorem anchoredTableAt {s : Shape} {b m d e c o len : ℕ} (B : NamedBlocks.B (s.size+1))
    (n : PortPoly.anchorCount c o m d e = s.size+1)
    (h : Tracks (networkTile b m d e c o s.size 0 len) B) :
    let N := joinB (PointGraph.zeroLast s.size) B
    ∀ i : Fin (AnchoredLayout.block N.core (s.size+1)).A.ne,
      (anchoredTable b m d e c o len).2 i.val = (AnchoredLayout.signal N.core N.name i).val := by
  rw [anchoredTable,n,Nat.add_sub_cancel]
  exact anchoredName B _ h

private theorem tableWord {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (j : Fin 4) (T : ℕ) (η : List Bool) :
    wordTable (SignalGeometry.word E j T η) = anchoredTable (bitLen p) (blockCount (bitLen p))
      (GateSemantics.d p) (GateSemantics.e p) (RoutesV2.copies j) (RoutesV2.outputs j) η.length := by
  have hj : PortPoly.idx (SignalGeometry.word E j T η) = j.val ∧ PortPoly.prefixBits (SignalGeometry.word E j T η) = η := by
    simp [PortPoly.idx,PortPoly.prefixBits,SignalGeometry.word,M89S1.queryWord,DetDLP_W1_Queries.third,DetDLP_W1_Queries.second]
  simp only [wordTable,SignalGeometry.prime_word,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,
    S8H.PointAddresses.wires_eq (GateSemantics.hd p),hj.1,hj.2]
  rfl

section
attribute [local irreducible] RoutesV2.network networkTile Tracks AnchoredLayout.block joinB

set_option maxHeartbeats 450000 in
private theorem registerAt {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (hm : 1 ≤ m) (j : Fin 4) (T : ℕ) (η : List Bool) (i : Fin (SignalGeometry.core E hm j T η).A.ne) :
    (anchoredTable (bitLen p) m (GateSemantics.d p) (GateSemantics.e p) (RoutesV2.copies j)
      (RoutesV2.outputs j) η.length).2 i.val = ((SignalGeometry.wires E hm j T η).signal i).val := by
  let d := GateSemantics.d p
  let e := GateSemantics.e p
  let s := RoutesV2.bank j m d e
  let B : NamedBlocks.B (s.size+1) := RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E)
    E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val j η id
  let t := networkTile (bitLen p) m d e (RoutesV2.copies j) (RoutesV2.outputs j) s.size 0 η.length
  have h : Tracks t B := @networkTracks m d 0 s (GateSemantics.hd p) hm p T (GateSemantics.coeff E)
    E.b₂.val (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val j η id (fun a => (Nat.zero_add _).symm)
  exact @anchoredTableAt s (bitLen p) m d e (RoutesV2.copies j) (RoutesV2.outputs j) η.length B
    (SignalGeometry.anchor_eq m d e j) h i

end

theorem signal_word {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool)
    (i : Fin (SignalGeometry.core E hm j T η).A.ne) :
    signal (SignalGeometry.word E j T η) i.val = ((SignalGeometry.wires E hm j T η).signal i).val :=
  (congrArg (fun r : R => r.2 i.val) (tableWord E j T η)).trans (registerAt E hm j T η i)

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H4.TracksPoly

private theorem wordGoodAux {α : Type} [Enc α] (w : α → List Bool) (hw : PolyT w) :
    Good fun x => wordTable (w x) := by
  let b := fun x => S8G.FpMoment.Code.width (S8M.PortPoly.prime (w x))
  let j := fun x => PortPoly.idx (w x)
  let m := fun x => S8G.FpMoment.Code.slots (b x)
  let d := fun x => b x+1
  let e := fun x => S8H.PointAddresses.wires (d x)
  have hb : PolyT b := S8G.FpMoment.Code.width_poly (PolyT.comp (g:=w) DetDLP.S8N.PortPoly.prime_poly hw)
  have hd : PolyT d := PolyT.add hb (PolyT.const 1)
  have he : PolyT e := S8H.PointAddresses.mul_poly.nb hd
  have hm : PolyT m := S8G.FpMoment.Code.slots_poly hb
  have hj : PolyT j := PolyT.comp (g:=w) PortPoly.idx_poly hw
  have hc : PolyT fun x => min (j x) 2 := by
    simp only [min_def]
    exact PolyT.ite' (PolyT.decide_le hj (PolyT.const 2)) hj (PolyT.const 2)
  have ho : PolyT fun x => if j x=3 then 1 else 0 :=
    PolyT.ite' (PolyT.decide_eq hj (PolyT.const 3)) (PolyT.const 1) (PolyT.const 0)
  exact anchoredGood hb hm hd he hc ho (PolyT.length (PolyT.comp (g:=w) PortPoly.prefix_poly hw))

theorem signal_poly : PolyT fun z : List Bool × ℕ => signal z.1 z.2 :=
  (wordGoodAux (@Prod.fst (List Bool) ℕ) (PolyT.fst PolyT.id')).2 Prod.snd (PolyT.snd PolyT.id')

end DetDLP.S8N.MomentSignal
end
end

set_option autoImplicit false
open DetDLP DetDLP.S8N

set_option autoImplicit false
open DetDLP DetDLP.S8N DetDLP.S8H0 RegisterMap NamedBlocks
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∃ signal : List Bool → ℕ → ℕ,
      Groundwork.PolyT (fun z : List Bool × ℕ => signal z.1 z.2) ∧
      ∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
        (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool),
        let m := blockCount (bitLen p)
        let s := RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)
        let N := joinB (PointGraph.zeroLast s.size)
          (RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E) E.b₂.val
            (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η id)
        ∀ i : Fin (AnchoredLayout.block N.core (s.size+1)).A.ne,
          signal (M89S1.queryWord 2 (encodeCurveInput p E) [countWord j.val,countWord T,η]) i.val =
            ((AnchoredLayout.wiring N.core N.name).signal i).val := by
  refine ⟨MomentSignal.signal, MomentSignal.signal_poly, ?_⟩
  intro p hp E hm j T η
  dsimp only
  intro i
  exact MomentSignal.signal_word E hm j T η i
