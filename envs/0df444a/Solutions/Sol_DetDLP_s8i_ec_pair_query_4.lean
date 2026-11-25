-- Prove2me | solution 4 for DetDLP.s8i_ec_pair_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T10:17:27.809306+00:00
-- url     : https://prove2.me/submissions/9272085b-028f-488e-8c8f-2a5b5fbf6d16

import Definitions.Def_DetDLP_S8M_AtomRunFits
import Definitions.Def_DetDLP_S8M_StepBaseNat
import Definitions.Def_DetDLP_S8M_MakePacket_v2
import Definitions.Def_DetDLP_S8M_PortBankRows

set_option autoImplicit false

namespace DetDLP.S8M.RealBaseFits
open S8H0 S8H.MakeCombinators S8H.PointAddresses M89S1 Groundwork

def raw (w : List Bool) : NC :=
  let b := S8G.FpMoment.Code.width (ECPair.Packet.prime w)
  let m := S8G.FpMoment.Code.slots b
  let d := b+1
  StepBaseNat.baseN m d (wires d) b (ECPair.Packet.prefixBits w).length

theorem rawWord {p T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool) :
    raw (ECPair.word E T S X η) =
      StepBaseNat.baseN (blockCount (bitLen p)) (GateSemantics.d p)
        (GateSemantics.e p) (bitLen p) η.length := by
  have hw := ECPair.Packet.fields E T S X η
  simp only [raw, hw.1, hw.2.2.2.2, S8G.FpMoment.Code.width_eq, S8G.FpMoment.Code.slots_eq]
  rw [wires_eq (GateSemantics.hd p)]

theorem rawEff {α : Type} [Enc α] {w : α → List Bool} (hw : PolyT w) : Eff (fun x => raw (w x)) := by
  let b := fun x => S8G.FpMoment.Code.width (ECPair.Packet.prime (w x))
  have hb : PolyT b := S8G.FpMoment.Code.width_poly (PolyT.comp ECPair.Packet.prime_poly hw)
  have hd := PolyT.add hb (PolyT.const 1)
  exact StepBaseNat.baseN_eff (S8G.FpMoment.Code.slots_poly hb) hd
    (EffCombinators.wiresP hd) hb (PolyT.length (PolyT.comp ECPair.Packet.prefix_poly hw))

end DetDLP.S8M.RealBaseFits

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.AtomAlignmentProof.AtomBaseFit
open S8H0 RegisterMap GateRoutes RangeRows NamedBlocks HashRows RenamedFits EffCombinators RouteLift AtomRunFits
open S8H.MakeCombinators

variable {d e l : ℕ} (o pin : ℕ) (f : Fin ((GateRoutes.S d e).size+1) → Fin l)
variable (hp : pin = (f (Fin.last _)).val) (hr : ∀ a, Source f (.reg a) = o + a.index.val)

include hp hr in
theorem rangeFit (p : ℕ) :
    let x := o+1; let y := x+(3*d+1); let rng := rangeN d pin
    RF f (catN (catN (rng x) (rng y)) (manyN 6 fun g => catN (rng (Z o d e g)) (rng (Z o d e g+(3*d+1))))) (RangeRows.block d e p) := by
  dsimp only
  apply RouteLift.cat_map_spec
  case' ha => apply RouteLift.cat_map_spec <;> apply RenamedFits.checker _ _ _ hp
  case' hb => apply RouteLift.many_map_spec; intro g; apply RouteLift.cat_map_spec <;> apply RenamedFits.checker _ _ _ hp
  all_goals intro a; rw [hr]
  all_goals dsimp [xa,ya,oa,ra,Z,stride,Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Shape.size,RegisterMap.mul,triple,run,finProdFinEquiv]
  all_goals ring

include hp in
theorem wname {o' : ℕ} (P : Path (triple d) (S d e)) (h : ∀ a, o' + a.index.val = Source f (.reg (P a))) :
    WNames f (wd o' d pin) (rword P) := by
  intro j; unfold rword word padded wd; split_ifs with hlt
  · exact h (.fst (.word ⟨j,hlt⟩))
  · exact hp

variable {o pin f} in
include hp hr in
theorem opsCore (g : Fin 6) (c : Coeff) :
    let w := fun b => wd b d pin; let x := o+1; let y := x+(3*d+1); let z := Z o d e
    WNames f (fun j => if g.val=2 then w (z 1) j else if g.val=4 then w (z 3) j else if g.val=5 then w (z 4) j else pin) (operands c g.castSucc).1 ∧
    WNames f (fun j => if g.val=1 then w (z 0) j else if g.val=2 then w y j else w x j) (operands c g.castSucc).2.1 ∧
    WNames f (fun j => if g.val=0 then w y j else pin) (operands c g.castSucc).2.2 := by
  have Hx : WNames f (wd (o+1) d pin) (rword xa) := by
    apply wname _ _ hp; intro a; rw [hr]; dsimp [xa,Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,triple]; omega
  have Hy : WNames f (wd (o+1+(3*d+1)) d pin) (rword ya) := by
    apply wname _ _ hp; intro a; rw [hr]; dsimp [ya,Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,triple]; omega
  have Ho (i : Fin 7) : WNames f (wd (Z o d e i) d pin) (rword (oa i)) := by
    apply wname _ _ hp; intro a; rw [hr]; dsimp [oa,Z,stride,Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Shape.size,RegisterMap.mul,triple,run,finProdFinEquiv]; ring
  have P (n : ℕ) : WNames f (fun _ => pin) (pub n) := fun _ => hp
  fin_cases g <;> refine ⟨?_,?_,?_⟩ <;> first | exact Hx | exact Hy | exact P _ | exact Ho 0 | exact Ho 1 | exact Ho 3 | exact Ho 4

end DetDLP.S8M.AtomAlignmentProof.AtomBaseFit

namespace DetDLP.S8M.AtomAlignmentProof.AtomCoreRows

open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RenamedFits AtomRunFits

def coreHash (d e o pin g : ℕ) : NC :=
  let x := o+1
  let y := x+(3*d+1)
  let w := fun q => wd q d pin
  let z := Z o d e
  StepBaseNat.hashN d e pin (z g) (U o d e g)
    (fun j => if g=2 then w (z 1) j else if g=4 then w (z 3) j else if g=5 then w (z 4) j else pin)
    (fun j => if g=1 then w (z 0) j else if g=2 then w y j else w x j)
    (fun j => if g=0 then w y j else pin)

def curveCode (d e o : ℕ) : NC :=
  let x := o+1
  let y := x+(3*d+1)
  let z := Z o d e
  rowN d 5 fun j k =>
    if k=0 then o else if k=1 then x+j else if k=2 then y+j
    else if k=3 then z 2+j else z 5+j

theorem hashesFit {d l : ℕ} (hd : 1 ≤ d) (p : ℕ) (c : Coeff)
    (o pin : ℕ) (f : Fin ((S d (Routes.G hd)).size+1) → Fin l)
    (hp : pin = (f (Fin.last _)).val)
    (hr : ∀ a, Source f (.reg a) = o + a.index.val) :
    RF f (manyN 5 (coreHash d (Routes.G hd) o pin))
      (many 5 fun g => HashRows.block p (wires hd p c g.castSucc)) := by
  apply RouteLift.many_map_spec
  intro g
  obtain ⟨ha,hx,hb⟩ := AtomBaseFit.opsCore hp hr g c
  exact AtomRunFits.hashRun hd p c g.castSucc o pin f hp hr _ _ _ ha hx hb

end DetDLP.S8M.AtomAlignmentProof.AtomCoreRows

namespace DetDLP.S8M.AtomAlignmentProof.AtomCoreRows

open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RenamedFits AtomRunFits

theorem curveFit {d e l : ℕ} (o : ℕ) (f : Fin ((S d e).size+1) → Fin l)
    (hr : ∀ a, Source f (.reg a) = o + a.index.val) :
    RF f (curveCode d e o) (CurveRows.block d e) := by
  apply RenamedFits.row
  intro j k
  fin_cases k
  all_goals first
    | change o = Source f (.reg CurveRows.flag)
    | change o+1+j.val = Source f (.reg (CurveRows.xbit j))
    | change o+1+(3*d+1)+j.val = Source f (.reg (CurveRows.ybit j))
    | change Z o d e 2+j.val = Source f (.reg (CurveRows.outbit 2 j))
    | change Z o d e 5+j.val = Source f (.reg (CurveRows.outbit 5 j))
  all_goals erw [hr]
  all_goals simp only [CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,
    RouteLift.idxL,RouteLift.idxR,RouteLift.idxV,Z,stride,Shape.size,
    RegisterMap.mul,triple,run]
  all_goals dsimp [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,Shape.size,RegisterMap.mul,triple,
    run,EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv] <;> ring

end DetDLP.S8M.AtomAlignmentProof.AtomCoreRows

namespace DetDLP.S8M.AtomAlignmentProof.AtomSeedHashRows

open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RenamedFits AtomRunFits

theorem seedOffset (o d e : ℕ) : U o d e 7 = o + (S d e).size := by
  simp only [U, Z, stride, S, RegisterMap.bank, RegisterMap.mul, triple, run, Shape.size]
  omega

def seedHash (d e o pin : ℕ) : NC :=
  let seed := U o d e 7
  StepBaseNat.hashN d e pin (Z o d e 6) (U o d e 6)
    (wd seed d pin) (wd (o+1) d pin) (wd (seed+d) d pin)

theorem seedHashFit {d l : ℕ} (hd : 1 ≤ d) (p : ℕ) (c : Coeff)
    (o pin : ℕ) (f : Fin ((ECAtomSlot.slotShape d (Routes.G hd)).size+1) → Fin l)
    (hp : pin = (f (Fin.last _)).val)
    (hr : ∀ a, Source f (.reg a) = o + a.index.val) :
    RF f (seedHash d (Routes.G hd) o pin)
      (HashRows.block p (S8H4.Routes.network.six hd p c)) := by
  have hmask (b : Bool) (a : Addr (ECAtomSlot.slotShape d (Routes.G hd))) :
      Source f (.masked b a) = o + a.index.val := hr a
  have hpin (b : Bool) : Source f (.pin b) = pin := hp.symm
  apply RenamedFits.hash f p _ hp
  all_goals intro j
  all_goals dsimp only [S8H4.Routes.network.six, S8H4.Routes.network.a6Reg,
    S8H4.Routes.network.b6Reg, S8H4.Routes.network.coord, wires, wd, word,
    padded, quot, rword, Function.comp_apply]
  all_goals (try split_ifs) <;> first | exact (hpin _).symm | erw [hr] | erw [hmask]
  all_goals simp only [xa, oa, ra, runPath, m1, m2, aux, cm,
    RouteLift.idxL, RouteLift.idxR, RouteLift.idxV, Shape.size, Z, U, stride,
    S, RegisterMap.bank, RegisterMap.mul, triple, run, auxShape]
  all_goals dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd,
    EquivLike.coe, DFunLike.coe, EquivLike.toFunLike, Equiv.instEquivLike,
    Shape.size, RegisterMap.mul, triple, run, auxShape, finProdFinEquiv]
  all_goals ring

end DetDLP.S8M.AtomAlignmentProof.AtomSeedHashRows

namespace DetDLP.S8M.AtomAlignmentProof.AtomSeedRows

open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RenamedFits AtomRunFits
open AtomSeedHashRows

def thresholdCode (d e o pin : ℕ) : NC :=
  let seed := U o d e 7
  colN (d+1) (wd (Z o d e 6) d pin) (wd (seed+2*d) d pin)
    (fun _ => pin) (seed+3*d+·)

def thresholdRows (d e T : ℕ) : B ((ECAtomSlot.slotShape d e).size+1) :=
  NamedBlocks.add (n:=d+1) true
    (pad fun i : Fin d => Ref.reg (.fst (oa 6 (.fst (.word i)))))
    (pad fun i : Fin d => .reg (.snd (.snd (.snd (.fst (.word i))))))
    (fun i => .pin (T.testBit i))
    (fun i => .reg (.snd (.snd (.snd (.snd (.word i))))))

theorem thresholdFit {d e l : ℕ} (o pin T : ℕ)
    (f : Fin ((ECAtomSlot.slotShape d e).size+1) → Fin l)
    (hp : pin = (f (Fin.last _)).val)
    (hr : ∀ a, Source f (.reg a) = o + a.index.val) :
    RF f (thresholdCode d e o pin) (thresholdRows d e T) := by
  apply RenamedFits.col
  all_goals intro j
  all_goals try dsimp only [wd, pad]
  all_goals (try split_ifs) <;> first | exact hp | erw [hr]
  all_goals simp only [seedOffset, oa, RouteLift.idxL, RouteLift.idxR,
    RouteLift.idxV, Shape.size, Z, stride]
  all_goals dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd,
    EquivLike.coe, DFunLike.coe, EquivLike.toFunLike, Equiv.instEquivLike,
    Shape.size, RegisterMap.mul, triple, run, finProdFinEquiv]
  all_goals ring

def liftRef {l s : Shape} (path : Path l s) : Ref l → Ref s
  | .reg a => .reg (path a)
  | .masked v a => .masked v (path a)
  | .pin v => .pin v

def seedRowCode (d e o pin : ℕ) : NC :=
  let y := o+1+(3*d+1)
  let seed := U o d e 7
  rowN d 7 fun j k =>
    if k=0 then wd y d pin 0 else if k=1 then seed+j
    else if k=2 then seed+d+j else pin

theorem seedRowsFit {d e : ℕ} {s : Shape} (hd : 1 ≤ d) (o : ℕ)
    (path : Path (ECAtomSlot.slotShape d e) s)
    (hr : ∀ a, (path a).index.val = o + a.index.val)
    (a₀ b₀ a₁ b₁ : ℕ) (test : Fin d → (Fin 7 → Bool) → Bool) :
    Fits (seedRowCode d e o s.size)
      (rows d 7 (fun j => ![
        liftRef path (S8H4.Routes.network.coord ya 0),
        liftRef path (S8H4.Routes.network.a6Reg j),
        liftRef path (S8H4.Routes.network.b6Reg j),
        pub a₀ j, pub b₀ j, pub a₁ j, pub b₁ j]) test) := by
  apply row_spec
  intro j k
  fin_cases k <;> simp [S8H4.Routes.network.coord, GateRoutes.word, HashRows.padded,
    show 0 < d by omega, S8H4.Routes.network.a6Reg, S8H4.Routes.network.b6Reg,
    liftRef, pub, Ref.source, wd, seedOffset, ya, RouteLift.idxL, RouteLift.idxR,
    Addr.index, Fin.castAdd, Fin.natAdd, Shape.size, triple]
  all_goals erw [hr]
  all_goals simp only [RouteLift.idxL,RouteLift.idxR,Shape.size,triple,Addr.index,
    Fin.castAdd,Fin.castLE,Fin.natAdd]; ring

end DetDLP.S8M.AtomAlignmentProof.AtomSeedRows

namespace DetDLP.S8M.AtomAlignmentProof.RealAtomRouting

open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RenamedFits AtomRunFits
open RouteLift AtomCoreRows AtomSeedHashRows AtomSeedRows

attribute [local irreducible] catN manyN rowN rangeN colN genHashN
  joinB RangeRows.many HashRows.block

/-- The effective natural-number code of one seed-query slot has exactly
the local gate layout and register names of its physical block. -/
theorem atom_fits {m d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (S₀ : Routes.SeedData m) (i : Fin (2*m)) :
    Fits (AtomMapNat.atomN m d (Routes.G hd) i.val)
      (Routes.atomRows hd p T c S₀ i) := by
  let e := Routes.G hd
  let o := i.val * (ECAtomSlot.slotShape d e).size
  let pin := (Routes.bank m d e).size
  let f := ECAtomSlot.route (Routes.A (d:=d) (e:=e) i)
  have pathOffsets (a : Addr (ECAtomSlot.slotShape d e)) :
      (Routes.A i a).index.val = o+a.index.val := by
    simpa only [o, AtomMapNat.slot_size] using atom_at i a
  have hmap := route_val (Routes.A i) o pathOffsets
  have regIndex (j : Fin (ECAtomSlot.slotShape d e).size) :
      (f j.castSucc).val = o+j.val := by
    simpa only [f, Fin.val_castSucc, if_neg (Nat.ne_of_lt j.isLt)] using hmap j.castSucc
  have hp : pin = (f (Fin.last _)).val := by
    simpa only [f, pin, Fin.val_last, if_true] using (hmap (Fin.last _)).symm
  have hr (a : Addr (ECAtomSlot.slotShape d e)) :
      Source f (.reg a) = o + a.index.val := regIndex a.index
  let g := f ∘ S8H4.Routes.network.embed (d:=d) (e:=e)
  have hp' : pin = (g (Fin.last _)).val := by
    dsimp only [g, Function.comp_apply, S8H4.Routes.network.embed]
    erw [Fin.lastCases_last]
    exact hp
  have hr' (a : Addr (S d e)) : Source g (.reg a) = o + a.index.val := by
    dsimp only [Source, Ref.source, g, Function.comp_apply, S8H4.Routes.network.embed]
    erw [Fin.lastCases_castSucc]
    exact regIndex _
  have hflag : RF f (rowN 1 1 fun _ _ => o)
      (rows 1 1 (fun _ _ => .reg (.fst CurveRows.flag)) (fun _ r => decide (r 0 = false))) := by
    apply RenamedFits.row
    intro j k
    change o = Source f (.reg (.fst CurveRows.flag))
    erw [hr]
    simp [CurveRows.flag, RouteLift.idxL, Addr.index, Fin.castAdd, Fin.castLE]
  let base := joinB (RangeRows.block d e p) <| joinB
    (many 5 fun g => HashRows.block p (wires hd p c g.castSucc)) (CurveRows.block d e)
  have hbase := cat_map_spec (f:=g) (AtomBaseFit.rangeFit o pin g hp' hr' p)
    (cat_map_spec (f:=g) (hashesFit hd p c o pin g hp' hr') (curveFit o g hr'))
  have hseed := cat_map_spec (f:=f) (seedHashFit hd p c o pin f hp hr)
    (cat_map_spec (f:=f) hflag (thresholdFit o pin T f hp hr))
  have hfixed := cat_map_spec (f:=f) (u:=⟨base.core, S8H4.Routes.network.embed ∘ base.name⟩)
    hbase hseed
  let seed := S₀ (Routes.idx i)
  have hlast := seedRowsFit hd o _ pathOffsets (seed false).1 (seed false).2 (seed true).1 (seed true).2
    (fun _ r => decide (r 1 = (if r 0 then r 5 else r 3) ∧ r 2 = (if r 0 then r 6 else r 4)))
  refine cat_spec hfixed ?_
  simpa only [seedRowCode, seed, o, e, U, Z, stride, S8H4.Routes.network.coord, GateRoutes.word, HashRows.padded,
    dif_pos (show 0 < d by omega), S8H4.Routes.network.a6Reg,
    S8H4.Routes.network.b6Reg, liftRef] using hlast

end DetDLP.S8M.AtomAlignmentProof.RealAtomRouting


namespace DetDLP.S8M.BankAlignmentProof.RepeatedBlockFits
open S8H0 RegisterMap NamedBlocks RangeRows S8H.PointAddresses
open S8H.MakeCombinators EffCombinators S8G.SeedAndAtomBank

private theorem quotientShift (c : Code) (hc : 0 < c.ne) (w : ℕ) (q : ℕ → ℕ) (i : ℕ) :
    i/c.ne*w + q (i%c.ne) =
      if i < c.ne then q i else w + ((i-c.ne)/c.ne*w + q ((i-c.ne)%c.ne)) := by
  by_cases h : i < c.ne
  · simp [h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.div_eq_sub_div hc (by omega), Nat.mod_eq_sub_mod (by omega)]
    rw [Nat.succ_mul]
    omega

private theorem splitCode (c : Code) (hc : 0 < c.ne) (n : ℕ) (f : ℕ → ℕ → ℕ) :
    repCode (n+1) c f =
      catN (c, f 0) (repCode n c (fun j => f (j+1))) := by
  apply Prod.ext
  · simp only [repCode, catN, sum, Code.mk.injEq]
    refine ⟨by rw [Nat.succ_mul, Nat.add_comm], by rw [Nat.succ_mul, Nat.add_comm],
      by rw [Nat.succ_mul, Nat.add_comm], ?_, ?_⟩
    · funext i; exact quotientShift c hc c.ng c.gate i
    · funext i; exact quotientShift c hc c.nb c.bit i
  · funext i
    change f (i/c.ne) (i%c.ne) =
      if i < c.ne then f 0 i else f ((i-c.ne)/c.ne+1) ((i-c.ne)%c.ne)
    by_cases h : i < c.ne
    · simp [h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [if_neg h, Nat.div_eq_sub_div hc (by omega), Nat.mod_eq_sub_mod (by omega)]

private theorem oneFits {k : ℕ} {c : Code} (f : ℕ → ℕ → ℕ) {b : B k}
    (h : Fits (c, f 0) b) : Fits (repCode 1 c f) b := by
  obtain ⟨hcore, hn⟩ := h
  refine ⟨⟨(Nat.one_mul _).trans hcore.ng, (Nat.one_mul _).trans hcore.nb,
    (Nat.one_mul _).trans hcore.ne, ?_, ?_⟩, ?_⟩
  all_goals intro i
  all_goals have hi : i.val < c.ne := by rw [hcore.ne]; exact i.isLt
  · simpa [repCode, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] using hcore.gate i
  · simpa [repCode, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] using hcore.bit i
  · simpa [repCode, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] using hn i

theorem manyFits {k : ℕ} (c : Code) (hc : 0 < c.ne) (n : ℕ)
    (f : ℕ → ℕ → ℕ) (bs : Fin (n+1) → B k)
    (h : ∀ j : Fin (n+1), Fits (c, f j.val) (bs j)) :
    Fits (repCode (n+1) c f) (many n bs) := by
  induction n generalizing f with
  | zero => exact oneFits f (h 0)
  | succ n ih =>
    rw [splitCode c hc]
    exact cat_spec (h 0) (ih (fun j => f (j+1)) (fun j => bs j.succ) (fun j => h j.succ))

theorem allFits {s : Shape} (n : ℕ) (hn : 0 < n) (f : ℕ → NC) (hf : 0 < (f 0).1.ne)
    (core : ∀ j : ℕ, (f j).1 = (f 0).1)
    (bs : Fin n → B (s.size+1)) (h : ∀ j : Fin n, Fits (f j.val) (bs j)) :
    Fits (repeated n f) (allRows n bs) := by
  cases n with
  | zero => omega
  | succ n =>
    apply manyFits _ hf n
    intro j
    rw [← core j.val]
    exact h j

end DetDLP.S8M.BankAlignmentProof.RepeatedBlockFits

namespace DetDLP.S8M.BankAlignmentProof.RepeatedTileCore
open S8H0 RegisterMap S8H.MakeCombinators S8H.PointAddresses EffCombinators

private theorem catCore {a b x y : NC} (ax : a.1 = x.1) (by' : b.1 = y.1) :
    (catN a b).1 = (catN x y).1 := congrArg₂ sum ax by'

private theorem manyCore (n : ℕ) {a b : ℕ → NC} (ab : ∀ j, (a j).1 = (b j).1) :
    (manyN n a).1 = (manyN n b).1 := by
  induction n generalizing a b with
  | zero => simpa only [manyN_zero] using ab 0
  | succ n ih =>
    rw [manyN_succ, manyN_succ]
    exact catCore (ab 0) (ih fun j => ab (j+1))

private theorem hashCore (d e pin z u pin' z' u' : ℕ) (a x b a' x' b' : ℕ → ℕ) :
    (StepBaseNat.hashN d e pin z u a x b).1 =
      (StepBaseNat.hashN d e pin' z' u' a' x' b').1 := rfl

attribute [local irreducible] catN manyN

theorem atomCore (m d e j : ℕ) : (AtomMapNat.atomN m d e j).1 = (AtomMapNat.atomN m d e 0).1 := by
  unfold AtomMapNat.atomN
  dsimp only
  repeat' first | apply catCore | (apply manyCore; intro i)
  all_goals rfl

theorem mapCore (m d e j : ℕ) : (AtomMapNat.mapN m d e j).1 = (AtomMapNat.mapN m d e 0).1 := by
  unfold AtomMapNat.mapN
  dsimp only
  repeat' first | apply catCore | (apply manyCore; intro i)
  all_goals rfl

attribute [local irreducible] StepBaseNat.hashN

private theorem tileCore (d e pin u v o u' v' o' : ℕ) :
    (StepBaseNat.tile d e pin u v o).1 = (StepBaseNat.tile d e pin u' v' o').1 := by
  unfold StepBaseNat.tile
  dsimp only
  repeat' first | apply hashCore | apply catCore | (apply manyCore; intro i)
  all_goals rfl

theorem stepCore (m d e j : ℕ) : (StepBaseNat.stepN m d e j).1 = (StepBaseNat.stepN m d e 0).1 :=
  tileCore _ _ _ _ _ _ _ _ _

end DetDLP.S8M.BankAlignmentProof.RepeatedTileCore

namespace DetDLP.S8M.BankAlignmentProof.RealAtomBank
open S8H0 RegisterMap GateRoutes NamedBlocks S8H.MakeCombinators
open EffCombinators S8G.SeedAndAtomBank

/-- The atom bank uses quotient and remainder to address all gates in all slots. -/
theorem atomBankFits {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (S₀ : Routes.SeedData m) :
    Fits (repeated (2*m) (AtomMapNat.atomN m d (Routes.G hd)))
      (allRows (2*m) (Routes.atomRows hd p T c S₀)) := by
  apply RepeatedBlockFits.allFits _ (by omega)
  · change 0 < _ + d*7
    omega
  · exact RepeatedTileCore.atomCore _ _ _
  · exact DetDLP.S8M.AtomAlignmentProof.RealAtomRouting.atom_fits hd p T c S₀

end DetDLP.S8M.BankAlignmentProof.RealAtomBank

namespace DetDLP.S8M.BankAlignmentProof.ContiguousHashFit
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RouteLift
section Map
open private gw fstP sndP rwrd refw from Definitions.Def_DetDLP_S8M_ECMapRows

theorem hashFits {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p o : ℕ)
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

end Map

open private gw from Definitions.Def_DetDLP_S8N_ECAddRoutes

theorem addHashFits {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p o : ℕ)
    (path : Path (ECMapRows.slot d (Routes.G hd)) s)
    (hor : ∀ a, (path a).index.val = o + a.index.val)
    {a x b : ℕ → ℕ} {A X B : Word s}
    (ha : Names a A) (hx : Names x X) (hb : Names b B) :
    Fits (StepBaseNat.hashN d (Routes.G hd) s.size o (o + 11*d+2*(Routes.G hd)+3) a x b)
      (HashRows.block p (gw hd p A X B path)) :=
  hashFits hd p o path hor ha hx hb

end DetDLP.S8M.BankAlignmentProof.ContiguousHashFit

namespace DetDLP.S8M.BankAlignmentProof.MapAddressRows
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RouteLift
open private sp fstP sndP result remain rwrd ranges from Definitions.Def_DetDLP_S8M_ECMapRows

def z (o d e g : ℕ) := o+1+(3*d+1)+(3*d+1)+g*(16*d+2*e+6)

theorem mapOffset {m d e : ℕ} (i : Fin (2*m)) (a : Addr (ECMapRows.mapShape d e)) :
    (Routes.M i a).index.val = StepBaseNat.mapOff m d e i + a.index.val := by
  change 2*m*(ECAtomSlot.slotShape d e).size + (a.index.val + (ECMapRows.mapShape d e).size*i.val) =
    2*m*(ECAtomSlot.slotShape d e).size + i.val*(ECMapRows.mapShape d e).size + a.index.val
  ring

theorem slotOffset {d e : ℕ} {s : Shape} {o : ℕ} (path : Path (ECMapRows.mapShape d e) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) (g : Fin 4) (a : Addr (ECMapRows.slot d e)) :
    ((sp path g) a).index.val = z o d e g+a.index.val := by
  erw [h]
  dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, EquivLike.coe, DFunLike.coe,
    EquivLike.toFunLike, Equiv.instEquivLike, finProdFinEquiv,
    Shape.size, ECMapRows.slot, auxShape, RegisterMap.mul, triple, run, z]
  ring

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
    Fits (rangeN d s.size o) (checker p path) :=
  RenamedFits.checker id p path rfl (fun a => (h a).symm)

def rangeCode (d e o pin : ℕ) : NC :=
  let r := rangeN d pin
  catN (catN (r (o+1)) (r (o+1+(3*d+1))))
    (manyN 3 fun g => catN (r (z o d e g)) (r (z o d e g+(3*d+1))))

theorem rangesFit {d e o : ℕ} {s : Shape} (p : ℕ) (path : Path (ECMapRows.mapShape d e) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) :
    Fits (rangeCode d e o s.size) (ranges p path) := by
  unfold rangeCode ranges
  dsimp only
  apply cat_spec
  · apply cat_spec <;> apply rangeFits <;> intro a
    all_goals dsimp only [fstP, sndP]; erw [h]
    all_goals dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    all_goals omega
  · apply manyN_spec
    intro g
    apply cat_spec <;> apply rangeFits <;> intro a
    all_goals dsimp only [result, remain, fstP, sndP]
    all_goals erw [slotOffset path h]
    all_goals dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    all_goals omega

end DetDLP.S8M.BankAlignmentProof.MapAddressRows

namespace DetDLP.S8M.BankAlignmentProof.MapHashRows
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RouteLift MapAddressRows
open private sp fstP sndP result rwrd args4 gw maskEq from Definitions.Def_DetDLP_S8M_ECMapRows

def hashCode (d e o pin ix iy g : ℕ) : NC :=
  let out := z o d e
  let w := fun q => wd q d pin
  StepBaseNat.hashN d e pin (out g) (out g+11*d+2*e+3) (fun _ => pin)
    (fun j => if g=3 then w (out 2) j else if g=2 then w iy j else w ix j)
    (fun j => if g=2 then w (out 1) j else pin)

theorem resultNames {d e o : ℕ} {s : Shape} (path : Path (ECMapRows.mapShape d e) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) (g : Fin 4) :
    Names (wd (z o d e g) d s.size) (rwrd (result (sp path g))) := by
  apply wordNames
  intro a
  exact slotOffset path h g (.fst (.fst a))

attribute [local irreducible] Fits manyN HashRows.block StepBaseNat.hashN

private theorem operands {d e o ix iy : ℕ} {s : Shape} (p b2 a1 a3 : ℕ)
    (path : Path (ECMapRows.mapShape d e) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) {X Y : Word s}
    (hx : Names (wd ix d s.size) X) (hy : Names (wd iy d s.size) Y) (g : Fin 4) :
    let a := args4 p b2 a1 a3 X Y path g
    let w := fun k => wd k d s.size
    Names (fun _ => s.size) a.1 ∧
    Names (fun j => if g.val=3 then w (z o d e 2) j else if g.val=2 then w iy j else w ix j) a.2.1 ∧
    Names (fun j => if g.val=2 then w (z o d e 1) j else s.size) a.2.2 := by
  have hp (n : ℕ) : Names (fun _ => s.size) (pub n) := fun _ => rfl
  fin_cases g
  · exact ⟨hp _, hx, hp _⟩
  · exact ⟨hp _, hx, hp _⟩
  · exact ⟨hp _, hy, resultNames path h 1⟩
  · exact ⟨hp _, resultNames path h 2, hp _⟩

theorem mapHashesFit {d o ix iy : ℕ} {s : Shape} (hd : 1 ≤ d) (p b2 a1 a3 : ℕ)
    (path : Path (ECMapRows.mapShape d (Routes.G hd)) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) {X Y : Word s}
    (hx : Names (wd ix d s.size) X) (hy : Names (wd iy d s.size) Y) :
    Fits (manyN 3 (hashCode d (Routes.G hd) o s.size ix iy))
      (many 3 fun g => let a := args4 p b2 a1 a3 X Y path g
        HashRows.block p (gw hd p a.1 a.2.1 a.2.2 (sp path g))) := by
  apply manyN_spec
  intro g
  obtain ⟨ha,hx',hb⟩ := operands p b2 a1 a3 path h hx hy g
  exact ContiguousHashFit.hashFits hd p _ _ (slotOffset path h g) ha hx' hb

def maskCode (d a o t : ℕ) : NC :=
  rowN d 3 fun j k => if k=0 then a else if k=1 then o+j else t+j

theorem maskFit {d a o t : ℕ} {s : Shape} {F : Ref s} {O Z : Word s}
    (hflag : a = F.source.val)
    (ho : Names (wd o d s.size) O) (ht : Names (wd t d s.size) Z) :
    Fits (maskCode d a o t) (maskEq F O Z d) := by
  apply row_spec
  intro j k
  fin_cases k
  · exact hflag
  · simpa [wd, j.isLt] using ho j.val
  · simpa [wd, j.isLt] using ht j.val

end DetDLP.S8M.BankAlignmentProof.MapHashRows

namespace DetDLP.S8M.BankAlignmentProof.RealMapBank
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RouteLift MapAddressRows MapHashRows
open private fstP sndP rwrd sp result from Definitions.Def_DetDLP_S8M_ECMapRows

attribute [local irreducible] catN manyN rowN rangeN colN genHashN
  joinB RangeRows.many HashRows.block

theorem mapFits {m d : ℕ} (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (i : Fin (2*m)) :
    Fits (AtomMapNat.mapN m d (Routes.G hd) i.val)
      (Routes.mapRows (m:=m) hd p b2 a1 a3 i) := by
  let e := Routes.G hd
  let atom := i.val*(ECAtomSlot.slotShape d e).size
  let o := StepBaseNat.mapOff m d e i.val
  let pin := (Routes.bank m d e).size
  let path := Routes.M (d:=d) (e:=e) i
  let w := Routes.atomW (d:=d) (e:=e) i
  have oa (a : Addr (ECAtomSlot.slotShape d e)) : (Routes.A i a).index.val = atom+a.index.val := by
    simpa only [atom,AtomMapNat.slot_size] using atom_at i a
  have mo (a : Addr (ECMapRows.mapShape d e)) : (path a).index.val = o+a.index.val := mapOffset i a
  have af : atom = w.1.source.val := by
    change atom = (Routes.A i (.fst CurveRows.flag)).index.val
    erw [oa]
    rfl
  have ax : Names (wd (atom+1) d pin) w.2.1 := by
    apply wordNames (fun a => Routes.A i (.fst (xa a)))
    intro a; erw [oa]
    dsimp [xa, Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega
  have ay : Names (wd (atom+1+(3*d+1)) d pin) w.2.2 := by
    apply wordNames (fun a => Routes.A i (.fst (ya a)))
    intro a; erw [oa]
    dsimp [ya, Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega
  let out := sndP (fstP path)
  have ox : Names (wd (o+1) d pin) (rwrd (fstP out)) := by
    apply wordNames
    intro a
    dsimp only [out, fstP, sndP]
    erw [mo]
    dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega
  have oy : Names (wd (o+1+(3*d+1)) d pin) (rwrd (sndP out)) := by
    apply wordNames
    intro a
    dsimp only [out, fstP, sndP]
    erw [mo]
    dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega
  have flag : Fits (rowN 1 2 fun _ k => if k=0 then o else atom)
      (eqs 1 (fun _ => .reg (fstP (fstP path) .bit)) (fun _ => w.1)) := by
    apply row_spec
    intro j k
    fin_cases k
    · change o = (path _).index.val
      erw [mo]
      rfl
    · exact af
  exact cat_spec (rangesFit p path mo) (cat_spec (mapHashesFit hd p b2 a1 a3 path mo ax ay)
    (cat_spec flag (cat_spec (maskFit af ox (resultNames path mo 0)) (maskFit af oy (resultNames path mo 3)))))

theorem mapBankFits {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) :
    Fits (repeated (2*m) (AtomMapNat.mapN m d (Routes.G hd)))
      (S8G.SeedAndAtomBank.allRows (2*m) (Routes.mapRows (m:=m) hd p b2 a1 a3)) := by
  apply RepeatedBlockFits.allFits _ (by omega)
  · simp only [AtomMapNat.mapN, catN, S8H.PointAddresses.sum, rowN, BaseCode.rowsCode, Nat.one_mul]
    omega
  · exact RepeatedTileCore.mapCore _ _ _
  · exact mapFits hd p b2 a1 a3

end DetDLP.S8M.BankAlignmentProof.RealMapBank

open DetDLP DetDLP.S8M DetDLP.S8H0.GateRoutes DetDLP.S8H.MakeCombinators
open DetDLP.S8M.EffCombinators DetDLP.S8G.SeedAndAtomBank

theorem DetDLP.S8M.DirectTagSix.atomMaps {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d)
    (p T b2 a1 a3 : ℕ) (c : Coeff) (S₀ : Routes.SeedData m) :
    Fits (repeated (2*m) (AtomMapNat.atomN m d (Routes.G hd)))
      (allRows (2*m) (Routes.atomRows hd p T c S₀)) ∧
    Fits (repeated (2*m) (AtomMapNat.mapN m d (Routes.G hd)))
      (allRows (2*m) (Routes.mapRows (m:=m) hd p b2 a1 a3)) :=
  ⟨BankAlignmentProof.RealAtomBank.atomBankFits hm hd p T c S₀,
   BankAlignmentProof.RealMapBank.mapBankFits hm hd p b2 a1 a3⟩

namespace DetDLP.S8M.BankAlignmentProof.AddAddressRows
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RouteLift S8N.ECAddRoutes
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

end DetDLP.S8M.BankAlignmentProof.AddAddressRows

namespace DetDLP.S8M.BankAlignmentProof.AddOperandNames
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

end DetDLP.S8M.BankAlignmentProof.AddOperandNames

namespace DetDLP.S8M.BankAlignmentProof.AddControlRows
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

end DetDLP.S8M.BankAlignmentProof.AddControlRows

namespace DetDLP.S8M.BankAlignmentProof.RealAddTile
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

end DetDLP.S8M.BankAlignmentProof.RealAddTile

namespace DetDLP.S8M.BankAlignmentProof.FoldAddressWords
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes S8N.ECAddRoutes
open S8H.MakeCombinators EffCombinators StepBaseNat
open private slice outFlag outX outY from Definitions.Def_DetDLP_S8M_ECFoldRoutes

def pointNames {s : Shape} (d o : ℕ) (flag : Ref s) (x y : Word s) : Prop :=
  o = flag.source.val ∧ Names (wd (o+1) d s.size) x ∧ Names (wd (o+1+(3*d+1)) d s.size) y

theorem mapWords {m d e : ℕ} (i : Fin (2*m)) :
    let w := Routes.mapW (d:=d) (e:=e) i
    pointNames d (mapOff m d e i.val) w.1 w.2.1 w.2.2 := by
  let path := Routes.M (d:=d) (e:=e) i
  have h := MapAddressRows.mapOffset (d:=d) (e:=e) i
  refine ⟨?_,?_,?_⟩
  · change _ = (Routes.M i _).index.val
    erw [h]
    rfl
  · apply MapAddressRows.wordNames (fun a => path (.fst (.snd (.fst a))))
    intro a; dsimp only [path]; erw [h]
    dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega
  · apply MapAddressRows.wordNames (fun a => path (.fst (.snd (.snd a))))
    intro a; dsimp only [path]; erw [h]
    dsimp [Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega

theorem addOffset {m d e : ℕ} (j : Fin (2*m-1)) (a : Addr (addShape d e)) :
    ((slice (Routes.F (m:=m) (d:=d) (e:=e)) j) a).index.val =
      addOff m d e j.val+a.index.val := by
  change 2*m*(ECAtomSlot.slotShape d e).size +
    (2*m*(ECMapRows.mapShape d e).size + (a.index.val + (addShape d e).size*j.val)) =
      (2*m*(ECAtomSlot.slotShape d e).size + 2*m*(ECMapRows.mapShape d e).size) +
        j.val*(addShape d e).size+a.index.val
  ring

theorem outWords {m d e : ℕ} (j : Fin (2*m-1)) :
    let q := Routes.F (m:=m) (d:=d) (e:=e)
    pointNames d (addOff m d e j.val) (outFlag q j) (outX q j) (outY q j) := by
  let q := Routes.F (m:=m) (d:=d) (e:=e)
  have h := addOffset (d:=d) (e:=e) j
  refine ⟨?_,?_,?_⟩
  · change _ = (slice q j _).index.val
    erw [h]
    rfl
  · simpa [AddAddressRows.coord] using AddAddressRows.coordNames (slice q j) h 0
  · simpa [AddAddressRows.coord] using AddAddressRows.coordNames (slice q j) h 1

end DetDLP.S8M.BankAlignmentProof.FoldAddressWords

namespace DetDLP.S8M.BankAlignmentProof.RealFoldBank
open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes S8H.MakeCombinators
open EffCombinators StepBaseNat S8N.ECAddRoutes FoldAddressWords S8G.SeedAndAtomBank
open private slice foldStep outputFlag outputX outputY outFlag outX outY from
  Definitions.Def_DetDLP_S8M_ECFoldRoutes

def actualStep {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (j : Fin (2*m-1)) : B ((Routes.bank m d (Routes.G hd)).size+1) :=
  let a := Routes.mapW (Routes.first hm)
  let b := fun j => Routes.mapW (Routes.next j)
  foldStep hd p neg1 three c4 a.1 a.2.1 a.2.2
    (fun k => (b k).1) (fun k => (b k).2.1) (fun k => (b k).2.2) Routes.F j

attribute [local irreducible] Fits tile addBlock

theorem stepFits {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (j : Fin (2*m-1)) :
    Fits (stepN m d (Routes.G hd) j.val) (actualStep hm hd p neg1 three c4 j) := by
  let e := Routes.G hd
  let q := Routes.F (m:=m) (d:=d) (e:=e)
  have b := mapWords (d:=d) (e:=e) (Routes.next j)
  by_cases h0 : j.val = 0
  · have a := mapWords (d:=d) (e:=e) (Routes.first hm)
    simp only [stepN, actualStep, foldStep, if_pos h0, dif_pos h0]
    exact RealAddTile.tileFits hd p neg1 three c4 (slice q j) (addOffset j)
      a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2
  · have a := outWords (d:=d) (e:=e) (m:=m) (⟨j.val-1,by have := j.isLt; omega⟩ : Fin (2*m-1))
    simp only [stepN, actualStep, foldStep, if_neg h0, dif_neg h0]
    exact RealAddTile.tileFits hd p neg1 three c4 (slice q j) (addOffset j)
      a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2

theorem stepsFit {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p neg1 three c4 : ℕ) :
    Fits (repeated (2*m-1) (stepN m d (Routes.G hd)))
      (allRows (2*m-1) (actualStep hm hd p neg1 three c4)) := by
  apply RepeatedBlockFits.allFits _ (by omega)
  · simp only [stepN, tile, catN, S8H.PointAddresses.sum, rowN, BaseCode.rowsCode, Nat.one_mul]
    omega
  · exact RepeatedTileCore.stepCore _ _ _
  · exact stepFits hm hd p neg1 three c4

private theorem pinRows {s : Shape} {n o : ℕ} (f g : Fin n → Ref s)
    (hf : ∀ k, o+k.val = (f k).source.val) (hg : ∀ k, s.size = (g k).source.val)
    (test : Fin n → (Fin 2 → Bool) → Bool) :
    Fits (rowN n 2 fun j k => if k=0 then o+j else s.size) (rows n 2 (fun i => ![f i,g i]) test) := by
  apply row_spec
  intro i j; fin_cases j
  · exact hf i
  · exact hg i

theorem foldFits {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p neg1 three c4 : ℕ) (t : Routes.Target) :
    Fits (foldN m d (Routes.G hd)) (Routes.foldRows hd hm p neg1 three c4 t) := by
  let e := Routes.G hd
  let q := Routes.F (m:=m) (d:=d) (e:=e)
  have hn : 2*m-1 ≠ 0 := by omega
  let last : Fin (2*m-1) := ⟨2*m-1-1,by omega⟩
  let o := addOff m d e last.val
  have a := outWords (d:=d) (e:=e) last
  have hflag (j : Fin 1) : o+j.val = (outFlag q last).source.val := by
    rw [show j.val = 0 by omega, Nat.add_zero]; exact a.1
  have hx (j : Fin d) : o+1+j.val = (outX q last j).source.val := by
    simpa only [wd, if_pos j.isLt] using a.2.1 j.val
  have hy (j : Fin d) : o+1+(3*d+1)+j.val = (outY q last j).source.val := by
    simpa only [wd, if_pos j.isLt] using a.2.2 j.val
  simp only [foldN, Routes.foldRows, ECFoldRoutes.foldBlock, outputFlag, outputX, outputY,
    if_neg hn, dif_neg hn]
  exact cat_spec (pinRows _ _ hflag (fun _ => rfl) _) <|
    cat_spec (pinRows _ _ hx (fun _ => rfl) _) <|
    cat_spec (pinRows _ _ hy (fun _ => rfl) _) (stepsFit hm hd p neg1 three c4)

end DetDLP.S8M.BankAlignmentProof.RealFoldBank

set_option autoImplicit false
namespace DetDLP.S8M.PrefixDigits

open S8H0 RegisterMap NamedBlocks HashRows RangeRows GateRoutes
open S8H.MakeCombinators EffCombinators RouteLift
open private rwrd fstP from Definitions.Def_DetDLP_S8M_ECMapRows

private theorem wordNames {d o : ℕ} {s : Shape} (path : Path (triple d) s)
    (h : ∀ a, (path a).index.val = o+a.index.val) :
    Names (wd o d s.size) (rwrd path) := by
  intro j
  dsimp only [wd, rwrd, fstP, word, padded]
  split_ifs with hj
  · exact (h (.fst (.word ⟨j,hj⟩))).symm
  · rfl



def coordinate (d pin o b t : ℕ) : ℕ :=
  if t = 0 then o else if t < b+1 then wd (o+1) d pin (b-t)
  else wd (o+1+(3*d+1)) d pin (2*b-t)

private theorem atomWords {m d e : ℕ} (i : Fin (2*m)) :
    let o := i.val*(ECAtomSlot.slotShape d e).size
    let w := Routes.atomW (d:=d) (e:=e) i
    let pin := (Routes.bank m d e).size
    o = w.1.source.val ∧ Names (wd (o+1) d pin) w.2.1 ∧
      Names (wd (o+1+(3*d+1)) d pin) w.2.2 := by
  dsimp only
  have h (a : Addr (ECAtomSlot.slotShape d e)) : (Routes.A i a).index.val =
      i.val*(ECAtomSlot.slotShape d e).size+a.index.val := by
    simpa only [AtomMapNat.slot_size] using atom_at i a
  refine ⟨?_, ?_, ?_⟩
  · change _ = (Routes.A i (.fst CurveRows.flag)).index.val
    erw [h]
    rfl
  · apply wordNames (fun a => Routes.A i (.fst (xa a)))
    intro a
    erw [h]
    dsimp [xa, Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega
  · apply wordNames (fun a => Routes.A i (.fst (ya a)))
    intro a
    erw [h]
    dsimp [ya, Addr.index, Fin.castAdd, Fin.castLE, Fin.natAdd, Shape.size, triple]
    omega

theorem oneSlot {m d e : ℕ} (b : ℕ) (i : Fin (2*m)) :
    (Routes.digits (d:=d) (e:=e) b i).map (fun r => r.source.val) =
      List.ofFn (fun t : Fin (2*b+1) => coordinate d (Routes.bank m d e).size
        (i.val*(ECAtomSlot.slotShape d e).size) b t.val) := by
  have hw := atomWords (d:=d) (e:=e) i
  apply List.ext_getElem
  · simp [Routes.digits]; omega
  intro t h1 h2
  rw [List.getElem_ofFn, List.getElem_map]
  cases t with
  | zero => exact hw.1.symm
  | succ t =>
    simp only [Routes.digits, List.getElem_cons_succ, coordinate, Nat.succ_ne_zero, if_false]
    by_cases ht : t < b
    · rw [if_pos (by omega), List.getElem_append_left (by simpa using ht), List.getElem_ofFn]
      exact (hw.2.1 (b-(t+1))).symm
    · rw [if_neg (by omega), List.getElem_append_right (by simpa using Nat.le_of_not_gt ht),
        List.getElem_ofFn]
      have htb : t < 2*b := by simpa only [List.length_ofFn, Nat.succ_lt_succ_iff] using h2
      have idx : (⟨t-b,by omega⟩ : Fin b).rev.val = 2*b-(t+1) := by
        change b - (t-b+1) = _
        omega
      simpa only [List.length_ofFn, idx] using (hw.2.2 (2*b-(t+1))).symm

end DetDLP.S8M.PrefixDigits


set_option autoImplicit false
namespace DetDLP.S8M.PrefixDigits

open S8H0 RegisterMap NamedBlocks S8H.MakeCombinators

private theorem weave {α : Type} (m n : ℕ) (f : ℕ → α) :
    (List.finRange m).flatMap (fun i =>
      List.ofFn (fun t : Fin n => f ((i.val*2)*n+t.val)) ++
      List.ofFn (fun t : Fin n => f ((i.val*2+1)*n+t.val))) =
      List.ofFn (fun t : Fin (m*2*n) => f t.val) := by
  rw [List.ofFn_mul (m:=m*2) (n:=n), List.ofFn_mul (m:=m) (n:=2)]
  simp [List.flatMap_def, ← List.ofFn_id, List.map_ofFn, List.flatten_flatten,
    List.ofFn_succ, Function.comp_def]

private theorem numbered {m d e : ℕ} (b : ℕ) (i : Fin m) (t : Fin (2*b+1)) (k : Fin 2) :
    coordinate d (Routes.bank m d e).size
      ((if k.val=0 then (Routes.L i).val else (Routes.R i).val)*(ECAtomSlot.slotShape d e).size) b t.val =
      StepBaseNat.digit m d e b ((i.val*2+k.val)*(2*b+1)+t.val) := by
  let h := i.val*2+k.val
  let n := 2*b+1
  have hn : 0 < n := by dsimp [n]; omega
  have ht : t.val < n := t.isLt
  have hdiv : (h*n+t.val)/n = h := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht, Nat.zero_add]
  have hmod : (h*n+t.val)%n = t.val := by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ht]
  change _ = (let h' := (h*n+t.val)/n; let tr := (h*n+t.val)%n;
    if h'<2*m then coordinate d (Routes.bank m d e).size
      ((h'/2+(h'%2)*m)*(ECAtomSlot.slotShape d e).size) b tr else (Routes.bank m d e).size)
  simp only [hdiv, hmod]
  have hi := i.isLt
  fin_cases k <;> simp [h, show i.val*2 < 2*m by omega, show i.val*2+1 < 2*m by omega,
    show (i.val*2+1)/2 = i.val by omega, Nat.add_comm m i.val]

private theorem bankNames {m d e : ℕ} (b : ℕ) :
    (Routes.refs (m:=m) (d:=d) (e:=e) b).map (fun r => r.source.val) =
    List.ofFn (fun i : Fin (m*2*(2*b+1)) => StepBaseNat.digit m d e b i.val) := by
  rw [← weave]
  simp only [Routes.refs, List.map_flatMap, List.map_append, oneSlot]
  apply List.flatMap_congr
  intro i _
  apply congrArg₂ List.append
  · apply congrArg List.ofFn; funext t
    exact numbered b i t 0
  · apply congrArg List.ofFn; funext t
    exact numbered b i t 1

theorem prefixFits (m d e b : ℕ) (η : List Bool) :
    Fits (rowN η.length 1 fun i _ => StepBaseNat.digit m d e b i)
      (Routes.prefixRows (m:=m) (d:=d) (e:=e) b η) := by
  apply row_spec
  intro i _
  let R := Routes.refs (m:=m) (d:=d) (e:=e) b
  have H := bankNames (m:=m) (d:=d) (e:=e) b
  change R.map (fun r => r.source.val) = _ at H
  change StepBaseNat.digit m d e b i.val = (R[i.val]?.getD (.pin false)).source.val
  have lengthR : R.length = m*2*(2*b+1) := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length H
  by_cases h : i.val < R.length
  · have hk := congrArg (fun l : List ℕ => l[i.val]?) H
    have h' : i.val < m*2*(2*b+1) := by omega
    rw [List.getElem?_eq_getElem h, Option.getD_some]
    simpa only [List.getElem?_map, List.getElem?_eq_getElem h,
      List.getElem?_ofFn, dif_pos h', Option.map_some, Option.some.injEq,
      ] using hk.symm
  · have ht : 2*m ≤ i.val/(2*b+1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by
      rw [Nat.mul_comm 2 m]; omega)
    simp only [List.getElem?_eq_none (Nat.le_of_not_gt h), Option.getD_none]
    simp [StepBaseNat.digit, Nat.not_lt.mpr ht, NamedBlocks.Ref.source]

end DetDLP.S8M.PrefixDigits

open DetDLP.S8M DetDLP.S8H.MakeCombinators

theorem DetDLP.S8M.DirectTagSix.prefixRows (m d e b : ℕ) (η : List Bool) :
    Fits (rowN η.length 1 fun j _ => StepBaseNat.digit m d e b j)
      (Routes.prefixRows (m:=m) (d:=d) (e:=e) b η) :=
  PrefixDigits.prefixFits m d e b η

set_option autoImplicit false

namespace DetDLP.S8M.AnchoredAlignmentProof
open S8H0 RegisterMap NamedBlocks S8H.MakeCombinators

def anchored {s : Shape} (rows : B (s.size+1)) : B (s.size+1) :=
  let net := joinB (PointGraph.zeroLast s.size) rows
  ⟨AnchoredLayout.block net.core (s.size+1), AnchoredLayout.signal net.core net.name⟩

theorem anchoredFits {s : Shape} {c : NC} {rows : B (s.size+1)} (h : Fits c rows) :
    Fits (catN (anchorN (s.size+1) id) (catN (anchorN 1 (fun _ => s.size)) c))
      (anchored (s:=s) rows) := by
  let root : B (s.size+1) := ⟨⟨AnchoredLayout.anchors _, fun _ _ => true⟩, id⟩
  have hr : Fits (anchorN (s.size+1) id) root := ⟨AnchoredLayout.anchorModels _, fun _ => rfl⟩
  have hz : Fits (anchorN 1 fun _ => s.size) (PointGraph.zeroLast s.size) :=
    ⟨AnchoredLayout.anchorModels _, fun _ => rfl⟩
  exact cat_spec hr (cat_spec hz h)

end DetDLP.S8M.AnchoredAlignmentProof

open DetDLP DetDLP.S8M DetDLP.S8H0 DetDLP.S8H0.NamedBlocks
open DetDLP.S8H0.GateRoutes DetDLP.S8H.MakeCombinators

theorem DetDLP.S8M.AnchoredAlignmentProof.alignForTagSix {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d)
    (p T : ℕ) (c : Coeff) (S₀ : Routes.SeedData m) (b2 neg1 three c4 : ℕ)
    (η : List Bool) (t : Routes.Target) :
    let s := Routes.bank m d (Routes.G hd)
    let rows := Routes.networkAt hd hm p T c S₀ b2 neg1 three c4 η t
    let net := joinB (PointGraph.zeroLast s.size) rows
    Fits (StepBaseNat.baseN m d (Routes.G hd) (bitLen p) η.length)
      (⟨AnchoredLayout.block net.core (s.size+1), AnchoredLayout.signal net.core net.name⟩ : B (s.size+1)) := by
  obtain ⟨a,maps⟩ := DetDLP.S8M.DirectTagSix.atomMaps hm hd p T b2 c.a1 c.a3 c S₀
  have fold := DetDLP.S8M.BankAlignmentProof.RealFoldBank.foldFits hm hd p neg1 three c4 t
  have prefRows := DetDLP.S8M.DirectTagSix.prefixRows m d (Routes.G hd) (bitLen p) η
  exact AnchoredAlignmentProof.anchoredFits (s:=Routes.bank m d (Routes.G hd))
    (cat_spec a (cat_spec maps (cat_spec fold prefRows)))

set_option autoImplicit false

namespace DetDLP.S8M.RealBaseFits
open S8H0 RegisterMap NamedBlocks S8H.MakeCombinators

def anchored {s : Shape} (rows : B (s.size+1)) : B (s.size+1) :=
  let net := joinB (PointGraph.zeroLast s.size) rows
  ⟨AnchoredLayout.block net.core (s.size+1), AnchoredLayout.signal net.core net.name⟩

end DetDLP.S8M.RealBaseFits

namespace DetDLP.S8M.RealBaseFits
open S8H0 S8H S8H.MakeCombinators S8H.ECPointArithmetic M89S1 w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem copyLayout {p m T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ m) (S : ECSeed p m) (X : E.toAffine.Point) (η : List Bool) :
    let u := anchored (s:=Semantics.shape p m) (Semantics.rowsAt E hp hm S X η T)
    CopyCycle.layout u.core.A.gate (NamedWires.next u.name) = Semantics.layout E hp hm S X η T := rfl

theorem makeWordOfFit {p T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p)) (S : ECSeed p (blockCount (bitLen p)))
    (X : E.toAffine.Point) (η : List Bool)
    (h : Fits (StepBaseNat.baseN (blockCount (bitLen p)) (GateSemantics.d p)
      (GateSemantics.e p) (bitLen p) η.length)
      (anchored (s:=Semantics.shape p (blockCount (bitLen p))) (Semantics.rowsAt E hp hm S X η T))) :
    let w := ECPair.word E T S X η
    let g := w3_factorGraph (Semantics.layout E hp hm S X η T)
    let k := Bounds.scale (blockCount (bitLen p)) (bitLen p)
    fullMake raw MakePacketV2.sizeField w = encodeBTNInstance w g.subdivision k k 1 := by
  rw [← rawWord (T:=T) E S X η] at h
  have H := fullMake_spec (F:=raw) (s:=MakePacketV2.sizeField) (w:=ECPair.word E T S X η) h
  rw [copyLayout E hp hm S X η, MakePacketV2.sizeField_word E T S X η] at H
  exact H

end DetDLP.S8M.RealBaseFits

open DetDLP DetDLP.S8M DetDLP.S8H.MakeCombinators DetDLP.M89S1 DetDLP.w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.S8M.RealBaseFits.makeForTagSix {p T : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p)) (S : ECSeed p (blockCount (bitLen p)))
    (X : E.toAffine.Point) (η : List Bool) :
    let w := ECPair.word E T S X η
    let G := w3_factorGraph (Semantics.layout E hp hm S X η T)
    let k := Bounds.scale (blockCount (bitLen p)) (bitLen p)
    fullMake RealBaseFits.raw MakePacketV2.sizeField w = encodeBTNInstance w G.subdivision k k 1 :=
  RealBaseFits.makeWordOfFit E hp hm S X η
    (DetDLP.S8M.AnchoredAlignmentProof.alignForTagSix hm (S8H0.GateSemantics.hd p) p T
      (S8H0.GateSemantics.coeff E) (Semantics.seed S) E.b₂.val (-1 : ZMod p).val
      (3 : ZMod p).val (-27*E.c₄).val η (Semantics.target E hp X))

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks GateRoutes LocalGateEq PortPoly M89S1
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p))
  (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool) (T : ℕ)

set_option maxHeartbeats 600000 in
theorem bankfits :
    FitsG (PortPoly.body (ECPair.word E T S X η)) (Semantics.core E hp hm S X η T) := by
  let w := ECPair.word E T S X η
  change FitsG (PortPoly.body w) (Semantics.core E hp hm S X η T)
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ : prime w = p ∧ threshold w = T ∧ seed w = List.ofFn (ecBits S) ∧ target w = encodeNatListBin (pointCoords X) ∧ prefixBits w = η := ECPair.Packet.fields E T S X η
  have hc : coeff w = GateSemantics.coeff E := coeff_eq E T S X η
  have hb : bTwo w = E.b₂.val := bTwo_eq E T S X η
  have hct : cTerm w = (-27 * E.c₄).val := cTerm_eq E T S X η
  have ht := target_eq E X hp
  have ht₁ := congrArg Prod.fst ht
  have ht₂ := congrArg (fun z : Routes.Target => z.2.1) ht
  have ht₃ := congrArg (fun z : Routes.Target => z.2.2) ht
  dsimp only at ht₁ ht₂ ht₃
  have hone : 1 < p := Nat.lt_trans (by decide : 1 < 3) hp
  have hn : (-1 : ZMod p).val = p-1 := by rw [ZMod.val_neg_of_ne_zero, ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt hone]
  simp only [PortPoly.body,h₁,h₂,h₃,h₄,h₅,w5_M6Sort.decode_encode,hc,hb,hct,width,slots,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,pad_eq]
  rw [S8H.PointAddresses.wires_eq (GateSemantics.hd p),anchor_eq]
  refine catG_spec (A:=⟨AnchoredLayout.anchors _,fun _ _ => true⟩) (B:=(Semantics.net E hp hm S X η T).core) ⟨rfl,fun _ _ => rfl⟩ ?_
  refine catB ⟨rfl,fun g v => (zeroLast_local _ g v).symm⟩ ?_
  unfold Semantics.rowsAt Routes.networkAt
  refine catB (atomBankFits E T S η) (catB (mapBankFits E) (catB ?_
    (prefixFits (blockCount (bitLen p)) (bitLen p) (GateSemantics.d p)
      (GateSemantics.e p) (Nat.le_succ _) η)))
  have ha₁ : (GateSemantics.coeff E).a1 = E.a₁.val := rfl
  have ha₃ : (GateSemantics.coeff E).a3 = E.a₃.val := rfl
  rw [ha₁,ha₃,ht₁,ht₂,ht₃,hn,ZMod.val_ofNat]
  exact foldFits (GateSemantics.hd p) hm p (-27*E.c₄).val (Semantics.target E hp X)
end DetDLP.S8M.PortEval

set_option autoImplicit false
open DetDLP DetDLP.S8M DetDLP.S8H.PortCombinators DetDLP.M89S1 DetDLP.S8M.PortPoly DetDLP.w4_M5Network

theorem DetDLP.S8M.PortEval.evaluateForTagSix {p T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ blockCount (bitLen p)) (S : ECSeed p (blockCount (bitLen p)))
    (X : E.toAffine.Point) (η : List Bool)
    (v : Fin (w3_factorGraph (Semantics.layout E hp hm S X η T)).subdivision.nV)
    (a : Fin ((w3_factorGraph (Semantics.layout E hp hm S X η T)).subdivision.deg v) → Bool) :
    port (encodePortQuery (ECPair.word E T S X η) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph (Semantics.layout E hp hm S X η T)).subdivisionTensor
        (w3_factorChecks _ (Semantics.tests E hp hm S X η T)) v a then 1 else 0] := by
  exact fullPort_eval (F := PortPoly.body) (B := Semantics.core E hp hm S X η T)
    (W := Semantics.wires E hp hm S X η T) (DetDLP.S8M.PortEval.bankfits E hp hm S X η T) v a

set_option autoImplicit false

namespace DetDLP.S8M.RealMakeCapacity

open Groundwork S8H0 NamedBlocks GateRoutes
open S8H.MakeCombinators S8H.PointAddresses
open private cost cost_join cost_rows count atom_cost map_cost fold_cost bank_size
  from Definitions.Def_DetDLP_S8M_Bounds
open private unary_mul from Definitions.Def_DetDLP_W4_M5EvalFrontend

/-- Counts gates and incidences for the untrusted input's own prefix length. -/
def capacity (m d l : ℕ) := 600000*(m+1)*(d+1) + 2*l + 10

theorem model_budget {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (S : Routes.SeedData m) (b2 n three c4 : ℕ) (η : List Bool) (t : Routes.Target) (a : Code) :
    let R := Routes.networkAt hd hm p T c S b2 n three c4 η t
    let s := (Routes.bank m d (Routes.G hd)).size
    Models a (AnchoredLayout.block (joinB (PointGraph.zeroLast s) R).core (s+1)).A →
    a.ng + a.ne ≤ capacity m d η.length := by
  dsimp only
  intro ha
  let s := (Routes.bank m d (Routes.G hd)).size
  let R := Routes.networkAt hd hm p T c S b2 n three c4 η t
  have hb : s ≤ (2*m)*(60000*(d+1)) := bank_size hd
  have hAtom := count (Routes.atomRows hd p T c S) (fun i => atom_cost hd p T c S i)
  have hMap := count (Routes.mapRows (m:=m) hd p b2 c.a1 c.a3)
    (fun _ => map_cost hd p _ _ _ _ _ _ _)
  have hFold := fold_cost hd hm p n three c4 t
  have hr : cost R ≤ (2*m)*(36000*(d+1)) + ((2*m)*(21000*(d+1)) +
      ((3+6*d+(2*m)*(76000*(d+1))) + (η.length*1+η.length))) := by
    simp only [R, Routes.networkAt, cost_join, Routes.prefixRows, cost_rows]
    exact Nat.add_le_add hAtom (Nat.add_le_add hMap (Nat.add_le_add hFold (le_refl _)))
  rw [ha.ng, ha.ne]
  change (s+1+(1+R.core.A.ng))+(s+1+(1+R.core.A.ne)) ≤ _
  dsimp only [cost] at hr
  unfold capacity
  ring_nf at hb hr ⊢
  omega

variable {α : Type} [Enc α]

private theorem uConst (n : ℕ) : Unary (fun _ : α => n) := PolyT.const _

private theorem uAdd {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => f x + g x := by
  apply (PolyT.append hf hg).congr
  intro x
  exact (List.replicate_add ..).symm

theorem unary {m d l : α → ℕ} (hm : Unary m) (hd : Unary d) (hl : Unary l) :
    Unary fun x => 6*capacity (m x) (d x) (l x) := by
  have shape := unary_mul (unary_mul (uConst 600000) (uAdd hm (uConst 1))) (uAdd hd (uConst 1))
  exact unary_mul (uConst 6) (uAdd (uAdd shape (unary_mul (uConst 2) hl)) (uConst 10))

theorem cycle_bounds {m d l : ℕ} (a : NC) (h : a.1.ng+a.1.ne ≤ capacity m d l) :
    let c := cycle a
    c.ng+c.nb+c.ne ≤ 6*capacity m d l ∧ c.ne+c.ne ≤ 6*capacity m d l := by
  dsimp [cycle, CycleCode.code]
  omega

end DetDLP.S8M.RealMakeCapacity

namespace DetDLP.S8M.RealMake

open Groundwork S8H0 NamedBlocks GateRoutes S8H.PointAddresses S8H.MakeCombinators

/-- A fixed choice of numeric gate parameters suffices to bound the common layout dimensions. -/
def ShapeModels : Prop := ∀ (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (p : ℕ) (η : List Bool),
  let R := Routes.networkAt hd hm p 0 ⟨0,0,0,0,0⟩ (fun _ _ => (0,0)) 0 0 0 0 η (false,0,0)
  let s := (Routes.bank m d (Routes.G hd)).size
  Models (StepBaseNat.baseN m d (Routes.G hd) (bitLen p) η.length).1
    (AnchoredLayout.block (joinB (PointGraph.zeroLast s) R).core (s+1)).A

private abbrev width (w : List Bool) := S8G.FpMoment.Code.width (ECPair.Packet.prime w)
private abbrev slots (w : List Bool) := S8G.FpMoment.Code.slots (width w)
private abbrev prefixBits := ECPair.Packet.prefixBits

private theorem raw_budget (model : ShapeModels) (w : List Bool) :
    (RealBaseFits.raw w).1.ng + (RealBaseFits.raw w).1.ne ≤
      RealMakeCapacity.capacity (slots w) (width w+1) (prefixBits w).length := by
  let p := ECPair.Packet.prime w
  let d := width w + 1
  let m := slots w
  have b_eq : width w = bitLen p := S8G.FpMoment.Code.width_eq _
  have hm : 1 ≤ m := by
    change 1 ≤ S8G.FpMoment.Code.slots (width w)
    rw [S8G.FpMoment.Code.slots_eq]
    exact (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hd : 1 ≤ d := Nat.succ_pos _
  have hr : RealBaseFits.raw w = StepBaseNat.baseN m d (Routes.G hd) (bitLen p) (prefixBits w).length := by
    change StepBaseNat.baseN m d (wires d) (width w) (prefixBits w).length = _
    rw [b_eq, wires_eq hd]
  rw [hr]
  exact RealMakeCapacity.model_budget hm hd p 0 ⟨0,0,0,0,0⟩ (fun _ _ => (0,0)) 0 0 0 0
    (prefixBits w) (false,0,0) _ (model m d hm hd p (prefixBits w))

private theorem width_unary : Unary width :=
  Unary.of_length (PolyT.bits (PolyT.sub ECPair.Packet.prime_poly (PolyT.const 1)))

private theorem enumeration : Unary (fun w => 6*RealMakeCapacity.capacity (slots w)
    (width w+1) (prefixBits w).length) := by
  have add (n : ℕ) : Unary (fun w => width w + n) :=
    (PolyT.append width_unary (PolyT.const (List.replicate n ()))).congr
      (fun w => (List.replicate_add ..).symm)
  have hs : Unary slots := by
    have hp := S8G.FpMoment.Code.slots_poly (S8G.FpMoment.Code.width_poly ECPair.Packet.prime_poly)
    refine (PolyT.unary_min_length hp (add 2)).congr fun w => ?_
    have h : slots w ≤ width w+2 := by
      unfold slots
      rw [S8G.FpMoment.Code.slots_eq]
      exact S8G.FpMoment.blockUpper _
    simp only [List.length_replicate, min_eq_left h]
  exact RealMakeCapacity.unary hs (add 1) (Unary.of_length ECPair.Packet.prefix_poly)

theorem poly_of_model (model : ShapeModels) :
    PolyT (fullMake RealBaseFits.raw MakePacketV2.sizeField) := by
  let big := fun w => List.replicate (6*RealMakeCapacity.capacity (slots w) (width w+1) (prefixBits w).length) ()
  apply fullMake_poly (big := big) (RealBaseFits.rawEff (w := id) PolyT.id')
    (RealBaseFits.rawEff (PolyT.fst (PolyT.id' (α := List Bool × ℕ)))) MakePacketV2.sizeField_poly enumeration
  intro w
  simpa only [id_eq, big, List.length_replicate] using RealMakeCapacity.cycle_bounds _ (raw_budget model w)

end DetDLP.S8M.RealMake

namespace DetDLP.S8M.RealMake

open Groundwork S8H0 S8H.PointAddresses S8H.MakeCombinators
open private rows_spec from Definitions.Def_DetDLP_S8H0_BaseCode

private theorem shape_models : ShapeModels := by
  intro m d hm hd p η
  have banks := DetDLP.S8M.DirectTagSix.atomMaps hm hd p 0 0 0 0
    ⟨0,0,0,0,0⟩ (fun _ _ => (0,0))
  have f := (DetDLP.S8M.BankAlignmentProof.RealFoldBank.foldFits hm hd p 0 0 0 (false,0,0)).1
  exact sum_spec (AnchoredLayout.anchorModels _) (sum_spec (AnchoredLayout.anchorModels 1)
    (sum_spec banks.1.1 (sum_spec banks.2.1 (sum_spec f (rows_spec ..)))))

/-- Polynomial-time construction of the complete Tag 6 graph packet on every input word. -/
theorem make_poly : PolyT (fullMake RealBaseFits.raw MakePacketV2.sizeField) :=
  poly_of_model shape_models

end DetDLP.S8M.RealMake

open DetDLP DetDLP.S8M DetDLP.S8H.MakeCombinators

theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [6] := by
  intro _
  apply ECPair.tagIntro (fullMake RealBaseFits.raw MakePacketV2.sizeField) PortPoly.port
    16000000 RealMake.make_poly PortPoly.port_poly
  intro p _ hp curve _ T S X η hT hη
  have hm : 1 ≤ blockCount (bitLen p) := (by decide : 1 ≤ 2).trans (le_max_left ..)
  exact Bounds.realizes_of_eval (E:=curve) (hp:=hp) (hm:=hm) (S:=S) (X:=X) (η:=η) (T:=T) hT hη _ _
    (DetDLP.S8M.RealBaseFits.makeForTagSix curve hp hm S X η)
    (DetDLP.S8M.PortEval.evaluateForTagSix curve hp hm S X η)
