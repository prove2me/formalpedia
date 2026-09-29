-- Prove2me | solution 1 for Deformation.exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/97687f26-2612-5d3f-9293-5ef94712372e

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
import Theorems.Thm_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct
open Function

universe u v w

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map TruncWitt.map_map comulRingHom wittHom mem_wittHom_iff map_convMul_of_mem_wittHom map_counit_of_mem_wittHom counit_coeff_of_mem_wittHom map_mem_wittHom convPow_prime_apply_coeff_of_mem_wittHom"
namespace WittVMStep
p2m_open "Deformation"

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {B : Type v} [CommRing B] {S : Type w} [CommRing S]

theorem iterate_verschiebung_add (a b : WittVector p B) (n : ℕ) :
    (WittVector.verschiebung)^[n] (a + b) =
      (WittVector.verschiebung)^[n] a + (WittVector.verschiebung)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      map_add]

theorem coeff_select' (P : ℕ → Prop) (x : WittVector p B) (i : ℕ) [Decidable (P i)] :
    (WittVector.select P x).coeff i = if P i then x.coeff i else 0 := by
  rw [WittVector.coeff_select]
  unfold WittVector.selectPoly
  split_ifs <;> simp

theorem coeff_tail_of_lt (X : WittVector p B) {n i : ℕ} (hi : i < n) : (WittVector.tail n X).coeff i = 0 := by
  rw [WittVector.tail, coeff_select', if_neg (not_le.2 hi)]

theorem coeff_tail_self (X : WittVector p B) (n : ℕ) : (WittVector.tail n X).coeff n = X.coeff n := by
  rw [WittVector.tail, coeff_select', if_pos le_rfl]

theorem coeff_init_of_lt (X : WittVector p B) {n i : ℕ} (hi : i < n) :
    (WittVector.init n X).coeff i = X.coeff i := by
  rw [WittVector.init, coeff_select', if_pos hi]

theorem coeff_init_of_le (X : WittVector p B) {n i : ℕ} (hi : n ≤ i) :
    (WittVector.init n X).coeff i = 0 := by
  rw [WittVector.init, coeff_select', if_neg (not_lt.2 hi)]

theorem coeff_add_of_coeff_lt_eq_zero (X Z : WittVector p B) (n : ℕ) (hZ : ∀ i < n, Z.coeff i = 0) :
    (X + Z).coeff n = X.coeff n + Z.coeff n ∧ ∀ i < n, (X + Z).coeff i = X.coeff i := by
  have htail : ∀ i < n, (WittVector.tail n X).coeff i = 0 := fun i hi => coeff_tail_of_lt X hi
  set T := WittVector.tail n X + Z with hT
  have hT' : T = (WittVector.verschiebung)^[n] ((WittVector.tail n X).shift n + Z.shift n) := by
    rw [iterate_verschiebung_add, ← WittVector.eq_iterate_verschiebung htail,
      ← WittVector.eq_iterate_verschiebung hZ]
  have hTlt : ∀ i < n, T.coeff i = 0 := fun i hi => by
    rw [hT']; exact WittVector.iterate_verschiebung_coeff_eq_zero _ hi
  have hTn : T.coeff n = X.coeff n + Z.coeff n := by
    rw [hT']
    have := WittVector.iterate_verschiebung_coeff (p := p)
      ((WittVector.tail n X).shift n + Z.shift n) n 0
    rw [zero_add] at this
    rw [this, WittVector.add_coeff_zero, WittVector.shift_coeff, WittVector.shift_coeff, add_zero,
      coeff_tail_self]
  have hdisj : ∀ i, (WittVector.init n X).coeff i = 0 ∨ T.coeff i = 0 := fun i => by
    by_cases hi : i < n
    · exact Or.inr (hTlt i hi)
    · exact Or.inl (coeff_init_of_le X (not_lt.1 hi))
  have hXZ : X + Z = WittVector.init n X + T := by
    rw [hT, ← add_assoc, WittVector.init_add_tail]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hXZ, WittVector.coeff_add_of_disjoint n _ _ hdisj, hTn, coeff_init_of_le X le_rfl, zero_add]
  · rw [hXZ, WittVector.coeff_add_of_disjoint i _ _ hdisj, hTlt i hi, coeff_init_of_lt X hi, add_zero]

def zext (x : TruncatedWittVector p n B) : TruncatedWittVector p (n + 1) B :=
  WittVector.truncate (n + 1) x.out

def topW (n : ℕ) (b : B) : WittVector p B := WittVector.mk p fun i => if i = n then b else 0

def top (b : B) : TruncatedWittVector p (n + 1) B := WittVector.truncate (n + 1) (topW n b)

@[scoped simp] theorem coeff_topW (b : B) (i : ℕ) : (topW (p := p) n b).coeff i = if i = n then b else 0 := by
  simp only [topW, WittVector.coeff_mk]

private theorem _root_.Deformation.WittVMStep.coeff_out (x : TruncatedWittVector p n B) (i : ℕ) :
    x.out.coeff i = if h : i < n then x.coeff ⟨i, h⟩ else 0 := by
  by_cases h : i < n
  · rw [dif_pos h]; exact TruncatedWittVector.coeff_out x ⟨i, h⟩
  · rw [dif_neg h, TruncatedWittVector.out]
    change (WittVector.mk p fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0).coeff i = 0
    rw [WittVector.coeff_mk, dif_neg h]

p2m_export "Deformation.WittVMStep" "coeff_out"
theorem coeff_zext (x : TruncatedWittVector p n B) (i : Fin (n + 1)) :
    (zext x).coeff i = if h : (i : ℕ) < n then x.coeff ⟨i, h⟩ else 0 := by
  rw [zext, WittVector.coeff_truncate, coeff_out]

theorem coeff_zext_castSucc (x : TruncatedWittVector p n B) (i : Fin n) :
    (zext x).coeff i.castSucc = x.coeff i := by
  rw [coeff_zext, dif_pos (by exact i.is_lt)]
  rfl

@[scoped simp] theorem coeff_zext_last (x : TruncatedWittVector p n B) : (zext x).coeff (Fin.last n) = 0 := by
  rw [coeff_zext, dif_neg (by simp)]

@[scoped simp] theorem zext_zero : zext (0 : TruncatedWittVector p n B) = 0 :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_zext, TruncatedWittVector.coeff_zero]
    split_ifs
    · exact TruncatedWittVector.coeff_zero _ _ _ _
    · rfl

@[scoped simp] theorem coeff_top_last (b : B) : (top (p := p) (n := n) b).coeff (Fin.last n) = b := by
  rw [top, WittVector.coeff_truncate, coeff_topW, Fin.val_last, if_pos rfl]

theorem coeff_top_castSucc (b : B) (i : Fin n) : (top (p := p) b).coeff i.castSucc = 0 := by
  rw [top, WittVector.coeff_truncate, coeff_topW, if_neg]
  exact Nat.ne_of_lt i.is_lt

theorem ext_truncate_last {y y' : TruncatedWittVector p (n + 1) B}
    (h1 : TruncatedWittVector.truncate (Nat.le_succ n) y = TruncatedWittVector.truncate (Nat.le_succ n) y')
    (h2 : y.coeff (Fin.last n) = y'.coeff (Fin.last n)) : y = y' := by
  refine TruncatedWittVector.ext fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact h2
  · have := congrArg (TruncatedWittVector.coeff j) h1
    rwa [TruncatedWittVector.coeff_truncate, TruncatedWittVector.coeff_truncate] at this

@[scoped simp] theorem truncate_zext (x : TruncatedWittVector p n B) :
    TruncatedWittVector.truncate (Nat.le_succ n) (zext x) = x := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_truncate]
  exact coeff_zext_castSucc x i

@[scoped simp] theorem truncate_top (b : B) :
    TruncatedWittVector.truncate (Nat.le_succ n) (top (p := p) b) = 0 := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
  exact coeff_top_castSucc b i

theorem map_zext (f : B →+* S) (x : TruncatedWittVector p n B) :
    TruncWitt.map f (zext x) = zext (TruncWitt.map f x) := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncWitt.coeff_map, coeff_zext, coeff_zext]
  split_ifs with h
  · rw [TruncWitt.coeff_map]
  · rw [map_zero]

theorem map_top (f : B →+* S) (b : B) : TruncWitt.map f (top (p := p) (n := n) b) = top (f b) := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncWitt.coeff_map, top, top, WittVector.coeff_truncate, WittVector.coeff_truncate, coeff_topW,
    coeff_topW]
  split_ifs <;> simp

theorem coeff_add_top (U : TruncatedWittVector p (n + 1) B) (c : B) :
    (U + top c).coeff (Fin.last n) = U.coeff (Fin.last n) + c ∧
      TruncatedWittVector.truncate (Nat.le_succ n) (U + top c) =
        TruncatedWittVector.truncate (Nat.le_succ n) U := by
  obtain ⟨Y, rfl⟩ := WittVector.truncate_surjective p (n + 1) B U
  have key := coeff_add_of_coeff_lt_eq_zero Y (topW n c) n (fun i hi => by
    rw [coeff_topW, if_neg (Nat.ne_of_lt hi)])
  refine ⟨?_, ?_⟩
  · rw [top, ← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, Fin.val_last, key.1,
      coeff_topW, if_pos rfl]
  · rw [top, ← map_add]
    refine TruncatedWittVector.ext fun i => ?_
    rw [TruncatedWittVector.coeff_truncate, TruncatedWittVector.coeff_truncate,
      WittVector.coeff_truncate, WittVector.coeff_truncate]
    exact key.2 _ i.is_lt

theorem top_add (a b : B) : top (p := p) (n := n) (a + b) = top a + top b := by
  refine ext_truncate_last ?_ ?_
  · rw [(coeff_add_top _ b).2, truncate_top, truncate_top]
  · rw [(coeff_add_top _ b).1, coeff_top_last, coeff_top_last]

theorem top_zero : top (p := p) (n := n) (0 : B) = 0 := by
  have h := top_add (p := p) (n := n) (0 : B) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem top_injective : Injective (top (p := p) (n := n) (B := B)) := fun a b h => by
  have := congrArg (TruncatedWittVector.coeff (Fin.last n)) h
  rwa [coeff_top_last, coeff_top_last] at this

theorem eq_zext_add_top (y : TruncatedWittVector p (n + 1) B) :
    y = zext (TruncatedWittVector.truncate (Nat.le_succ n) y) + top (y.coeff (Fin.last n)) := by
  refine ext_truncate_last ?_ ?_
  · rw [(coeff_add_top _ _).2, truncate_zext]
  · rw [(coeff_add_top _ _).1, coeff_zext_last, zero_add]

end Witt

section Obstruction

variable (k : Type u) [CommRing k] {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable {B : Type v} [CommRing B] [Bialgebra k B]
variable {T : Type w} [CommRing T] [Algebra k T]

abbrev cv (g h : B →ₐ[k] T) : B →ₐ[k] T := (WithConv.toConv g * WithConv.toConv h).ofConv

def obsPt (g h : B →ₐ[k] T) (x : TruncatedWittVector p (m + 1) B) : T :=
  (zext (TruncWitt.map g.toRingHom x) + zext (TruncWitt.map h.toRingHom x)).coeff (Fin.last (m + 1))

def obs (x : TruncatedWittVector p (m + 1) B) : B ⊗[k] B :=
  obsPt k (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B)
    (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B) x

variable {k}

theorem map_cv_of_mem_wittHom {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (g h : B →ₐ[k] T) :
    TruncWitt.map (cv k g h).toRingHom x = TruncWitt.map g.toRingHom x + TruncWitt.map h.toRingHom x :=
  map_convMul_of_mem_wittHom hx (WithConv.toConv g) (WithConv.toConv h)

theorem zext_add_zext {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (g h : B →ₐ[k] T) :
    zext (TruncWitt.map g.toRingHom x) + zext (TruncWitt.map h.toRingHom x) =
      zext (TruncWitt.map (cv k g h).toRingHom x) + top (obsPt k g h x) := by
  refine ext_truncate_last ?_ ?_
  · rw [map_add, truncate_zext, truncate_zext, (coeff_add_top _ _).2, truncate_zext,
      map_cv_of_mem_wittHom hx]
  · rw [(coeff_add_top _ _).1, coeff_zext_last, zero_add]
    rfl

theorem map_obsPt {T' : Type*} [CommRing T'] [Algebra k T'] (L : T →ₐ[k] T') (g h : B →ₐ[k] T)
    (x : TruncatedWittVector p (m + 1) B) :
    L (obsPt k g h x) = obsPt k (L.comp g) (L.comp h) x := by
  unfold obsPt
  have h1 : TruncWitt.map L.toRingHom
      (zext (TruncWitt.map g.toRingHom x) + zext (TruncWitt.map h.toRingHom x)) =
      zext (TruncWitt.map (L.comp g).toRingHom x) + zext (TruncWitt.map (L.comp h).toRingHom x) := by
    rw [map_add, map_zext, map_zext, TruncWitt.map_map, TruncWitt.map_map]
    rfl
  rw [← h1, TruncWitt.coeff_map]
  rfl

theorem obsPt_eq_lift_obs (g h : B →ₐ[k] T) (x : TruncatedWittVector p (m + 1) B) :
    obsPt k g h x = Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _) (obs k x) := by
  have h1 : (Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B) = g :=
    AlgHom.ext fun b => by simp
  have h2 : (Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B) = h :=
    AlgHom.ext fun b => by simp
  rw [obs, map_obsPt, h1, h2]

theorem obsPt_cocycle {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (g h l : B →ₐ[k] T) :
    obsPt k (cv k g h) l x + obsPt k g h x = obsPt k g (cv k h l) x + obsPt k h l x := by
  have e1 := zext_add_zext hx g h
  have e2 := zext_add_zext hx (cv k g h) l
  have e3 := zext_add_zext hx h l
  have e4 := zext_add_zext hx g (cv k h l)
  have hassoc : cv k (cv k g h) l = cv k g (cv k h l) := by
    change (WithConv.toConv g * WithConv.toConv h * WithConv.toConv l).ofConv =
      (WithConv.toConv g * (WithConv.toConv h * WithConv.toConv l)).ofConv
    rw [mul_assoc]
  rw [← hassoc] at e4
  set G := zext (TruncWitt.map g.toRingHom x)
  set H := zext (TruncWitt.map h.toRingHom x)
  set Lx := zext (TruncWitt.map l.toRingHom x)
  set GH := zext (TruncWitt.map (cv k g h).toRingHom x)
  set HL := zext (TruncWitt.map (cv k h l).toRingHom x)
  set GHL := zext (TruncWitt.map (cv k (cv k g h) l).toRingHom x)
  have A1 : G + H + Lx = GHL + (top (obsPt k (cv k g h) l x) + top (obsPt k g h x)) := by
    rw [e1, add_right_comm GH, e2]
    exact add_assoc GHL _ _
  have A2 : G + H + Lx = GHL + (top (obsPt k g (cv k h l) x) + top (obsPt k h l x)) := by
    rw [add_assoc G, e3, ← add_assoc G, e4]
    exact add_assoc GHL _ _
  have := A1.symm.trans A2
  rw [add_right_inj, ← top_add, ← top_add] at this
  exact top_injective this

theorem obsPt_comm [Coalgebra.IsCocomm k B] {x : TruncatedWittVector p (m + 1) B}
    (hx : x ∈ wittHom k p (m + 1) B) (g h : B →ₐ[k] T) : obsPt k g h x = obsPt k h g x := by
  have e1 := zext_add_zext hx g h
  have e2 := zext_add_zext hx h g
  have hcomm : cv k g h = cv k h g := by
    change (WithConv.toConv g * WithConv.toConv h).ofConv = (WithConv.toConv h * WithConv.toConv g).ofConv
    rw [mul_comm]
  set G := zext (TruncWitt.map g.toRingHom x)
  set H := zext (TruncWitt.map h.toRingHom x)
  rw [add_comm G H, e2, hcomm, add_right_inj] at e1
  exact (top_injective e1).symm

theorem obsPt_one_left {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (h : B →ₐ[k] T) :
    obsPt k (1 : WithConv (B →ₐ[k] T)).ofConv h x = 0 := by
  have e := zext_add_zext hx (1 : WithConv (B →ₐ[k] T)).ofConv h
  have h1 : cv k (1 : WithConv (B →ₐ[k] T)).ofConv h = h := by
    change ((1 : WithConv (B →ₐ[k] T)) * WithConv.toConv h).ofConv = h
    rw [one_mul]
  have h0 : TruncWitt.map ((1 : WithConv (B →ₐ[k] T)).ofConv).toRingHom x = 0 := by
    have hfac : ((1 : WithConv (B →ₐ[k] T)).ofConv).toRingHom =
        (algebraMap k T).comp (Bialgebra.counitAlgHom k B).toRingHom := by
      refine RingHom.ext fun c => ?_
      exact AlgHom.convOne_apply c
    rw [hfac, ← TruncWitt.map_map, map_counit_of_mem_wittHom hx, map_zero]
  rw [h1, h0, zext_zero, zero_add] at e
  have e' : zext (TruncWitt.map h.toRingHom x) + top (obsPt k (1 : WithConv (B →ₐ[k] T)).ofConv h x) =
      zext (TruncWitt.map h.toRingHom x) + top 0 := by
    rw [top_zero, add_zero]; exact e.symm
  rw [add_right_inj] at e'
  exact top_injective e'

theorem obsPt_one_right {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (g : B →ₐ[k] T) :
    obsPt k g (1 : WithConv (B →ₐ[k] T)).ofConv x = 0 := by
  have e := zext_add_zext hx g (1 : WithConv (B →ₐ[k] T)).ofConv
  have h1 : cv k g (1 : WithConv (B →ₐ[k] T)).ofConv = g := by
    change (WithConv.toConv g * (1 : WithConv (B →ₐ[k] T))).ofConv = g
    rw [mul_one]
  have h0 : TruncWitt.map ((1 : WithConv (B →ₐ[k] T)).ofConv).toRingHom x = 0 := by
    have hfac : ((1 : WithConv (B →ₐ[k] T)).ofConv).toRingHom =
        (algebraMap k T).comp (Bialgebra.counitAlgHom k B).toRingHom := by
      refine RingHom.ext fun c => ?_
      exact AlgHom.convOne_apply c
    rw [hfac, ← TruncWitt.map_map, map_counit_of_mem_wittHom hx, map_zero]
  rw [h1, h0, zext_zero, add_zero] at e
  have e' : zext (TruncWitt.map g.toRingHom x) + top (obsPt k g (1 : WithConv (B →ₐ[k] T)).ofConv x) =
      zext (TruncWitt.map g.toRingHom x) + top 0 := by
    rw [top_zero, add_zero]; exact e.symm
  rw [add_right_inj] at e'
  exact top_injective e'

theorem obsPt_map {B' : Type*} [CommRing B'] [Bialgebra k B'] (f : B →ₐ[k] B') (g h : B' →ₐ[k] T)
    (x : TruncatedWittVector p (m + 1) B) :
    obsPt k g h (TruncWitt.map f.toRingHom x) = obsPt k (g.comp f) (h.comp f) x := by
  unfold obsPt
  rw [TruncWitt.map_map, TruncWitt.map_map]
  rfl

theorem zext_add_top_mem_wittHom {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    {u : B} (hu : Coalgebra.comul (R := k) u = u ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u + obs k x) :
    zext x + top u ∈ wittHom k p (m + 2) B := by
  rw [mem_wittHom_iff, map_add, map_add, map_add, map_zext, map_zext, map_zext, map_top, map_top,
    map_top]
  have e := zext_add_zext hx (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B)
    (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B)
  have hcv : (cv k (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B)
      (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B)).toRingHom = comulRingHom k B := by
    refine RingHom.ext fun b => ?_
    change ((WithConv.toConv _ * WithConv.toConv _) : WithConv (B →ₐ[k] B ⊗[k] B)) b = _
    rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
      Algebra.TensorProduct.lift_includeLeft_includeRight]
    rfl
  rw [hcv] at e
  change zext (TruncWitt.map (comulRingHom k B) x) + top (Coalgebra.comul (R := k) u) =
    zext (TruncWitt.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom x) +
      top ((Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B) u) +
    (zext (TruncWitt.map (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B).toRingHom x) +
      top ((Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B) u))
  rw [add_add_add_comm, e, hu, add_assoc (zext (TruncWitt.map (comulRingHom k B) x)), ← top_add,
    ← top_add, add_right_inj, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  congr 1
  change u ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u + obsPt k _ _ x = obsPt k _ _ x + (u ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u)
  rw [add_comm]

theorem truncate_zext_add_top (x : TruncatedWittVector p (m + 1) B) (u : B) :
    TruncatedWittVector.truncate (Nat.le_succ (m + 1)) (zext x + top u) = x := by
  rw [(coeff_add_top _ _).2, truncate_zext]

theorem coeff_zext_add_top_last (x : TruncatedWittVector p (m + 1) B) (u : B) :
    (zext x + top u).coeff (Fin.last (m + 1)) = u := by
  rw [(coeff_add_top _ _).1, coeff_zext_last, zero_add]

theorem coeff_zext_add_top_castSucc (x : TruncatedWittVector p (m + 1) B) (u : B) (i : Fin (m + 1)) :
    (zext x + top u).coeff i.castSucc = x.coeff i := by
  have := congrArg (TruncatedWittVector.coeff i) (truncate_zext_add_top (p := p) x u)
  rwa [TruncatedWittVector.coeff_truncate] at this

end Obstruction

section TensorForm

variable (k : Type u) [CommRing k] {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable {B : Type v} [CommRing B] [Bialgebra k B]

open Algebra.TensorProduct in

structure Cocycle₂ (B : Type v) [CommRing B] [Bialgebra k B] where

  c : B ⊗[k] B

  coc : (Algebra.TensorProduct.assoc k k k B B B) (map (Bialgebra.comulAlgHom k B) (AlgHom.id k B) c) +
      (Algebra.TensorProduct.assoc k k k B B B) (c ⊗ₜ[k] (1 : B)) =
    map (AlgHom.id k B) (Bialgebra.comulAlgHom k B) c + (1 : B) ⊗ₜ[k] c

  counit_left : map (Bialgebra.counitAlgHom k B) (AlgHom.id k B) c = 0

  counit_right : map (AlgHom.id k B) (Bialgebra.counitAlgHom k B) c = 0

variable {k}

section ObsCocycle

open Algebra.TensorProduct

variable (k) (B)

abbrev j₁ : B →ₐ[k] B ⊗[k] (B ⊗[k] B) := includeLeft

abbrev j₂ : B →ₐ[k] B ⊗[k] (B ⊗[k] B) :=
  (includeRight : B ⊗[k] B →ₐ[k] B ⊗[k] (B ⊗[k] B)).comp (includeLeft : B →ₐ[k] B ⊗[k] B)

abbrev j₃ : B →ₐ[k] B ⊗[k] (B ⊗[k] B) :=
  (includeRight : B ⊗[k] B →ₐ[k] B ⊗[k] (B ⊗[k] B)).comp (includeRight : B →ₐ[k] B ⊗[k] B)

theorem comm₃ (u v : B ⊗[k] (B ⊗[k] B)) : Commute u v := mul_comm u v

theorem lift_j₁_j₂ :
    lift (j₁ k B) (j₂ k B) (fun _ _ => comm₃ k B _ _) =
      (Algebra.TensorProduct.assoc k k k B B B).toAlgHom.comp
        (includeLeft : B ⊗[k] B →ₐ[k] (B ⊗[k] B) ⊗[k] B) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp

theorem lift_j₂_j₃ :
    lift (j₂ k B) (j₃ k B) (fun _ _ => comm₃ k B _ _) =
      (includeRight : B ⊗[k] B →ₐ[k] B ⊗[k] (B ⊗[k] B)) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp

variable {k B}

theorem cv_apply {T : Type w} [CommRing T] [Algebra k T] (g h : B →ₐ[k] T)
    (hc : ∀ a b, Commute (g a) (h b)) (b : B) :
    cv k g h b = lift g h hc (Coalgebra.comul (R := k) b) := by
  change ((WithConv.toConv g * WithConv.toConv h) : WithConv (B →ₐ[k] T)) b = _
  rw [AlgHom.convMul_apply]

theorem obsPt_eq_lift_obs' {T : Type w} [CommRing T] [Algebra k T] (g h : B →ₐ[k] T)
    (hc : ∀ a b, Commute (g a) (h b)) (x : TruncatedWittVector p (m + 1) B) :
    obsPt k g h x = Algebra.TensorProduct.lift g h hc (obs k x) :=
  obsPt_eq_lift_obs g h x

variable (k B)

abbrev B3 : Type v := B ⊗[k] (B ⊗[k] B)

theorem lift_cv_j₁_j₂_j₃_tmul (a b : B) :
    lift (cv (T := B3 k B) k (j₁ k B) (j₂ k B)) (j₃ k B) (fun _ _ => comm₃ k B _ _) (a ⊗ₜ[k] b) =
      (Algebra.TensorProduct.assoc k k k B B B)
        (map (Bialgebra.comulAlgHom k B) (AlgHom.id k B) (a ⊗ₜ[k] b)) := by
  rw [lift_tmul, cv_apply _ _ (fun _ _ => comm₃ k B _ _), lift_j₁_j₂, map_tmul,
    Bialgebra.comulAlgHom_apply, AlgHom.id_apply, ← (Coalgebra.Repr.arbitrary k a).eq]
  simp only [map_sum, Finset.sum_mul, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem lift_j₁_cv_j₂_j₃_tmul (a b : B) :
    lift (j₁ k B) (cv (T := B3 k B) k (j₂ k B) (j₃ k B)) (fun _ _ => comm₃ k B _ _) (a ⊗ₜ[k] b) =
      map (AlgHom.id k B) (Bialgebra.comulAlgHom k B) (a ⊗ₜ[k] b) := by
  rw [lift_tmul, cv_apply _ _ (fun _ _ => comm₃ k B _ _), lift_j₂_j₃, map_tmul,
    Bialgebra.comulAlgHom_apply, AlgHom.id_apply, ← (Coalgebra.Repr.arbitrary k b).eq]
  simp only [map_sum, Finset.mul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.TensorProduct.one_def, Algebra.TensorProduct.tmul_mul_tmul]

theorem lift_cv_j₁_j₂_j₃ (z : B ⊗[k] B) :
    lift (cv (T := B3 k B) k (j₁ k B) (j₂ k B)) (j₃ k B) (fun _ _ => comm₃ k B _ _) z =
      (Algebra.TensorProduct.assoc k k k B B B)
        (map (Bialgebra.comulAlgHom k B) (AlgHom.id k B) z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => exact lift_cv_j₁_j₂_j₃_tmul k B a b

theorem lift_j₁_cv_j₂_j₃ (z : B ⊗[k] B) :
    lift (j₁ k B) (cv (T := B3 k B) k (j₂ k B) (j₃ k B)) (fun _ _ => comm₃ k B _ _) z =
      map (AlgHom.id k B) (Bialgebra.comulAlgHom k B) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => exact lift_j₁_cv_j₂_j₃_tmul k B a b

variable {B}

def obsCocycle {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B) :
    Cocycle₂ k B where
  c := obs k x
  coc := by
    have h := obsPt_cocycle (T := B3 k B) hx (j₁ k B) (j₂ k B) (j₃ k B)
    rw [obsPt_eq_lift_obs' _ _ (fun _ _ => comm₃ k B _ _),
      obsPt_eq_lift_obs' _ _ (fun _ _ => comm₃ k B _ _),
      obsPt_eq_lift_obs' _ _ (fun _ _ => comm₃ k B _ _),
      obsPt_eq_lift_obs' _ _ (fun _ _ => comm₃ k B _ _), lift_cv_j₁_j₂_j₃, lift_j₁_j₂,
      lift_j₁_cv_j₂_j₃, lift_j₂_j₃] at h
    simpa using h
  counit_left := by
    have h := obsPt_one_left hx (AlgHom.id k B)
    rw [obsPt_eq_lift_obs] at h
    have hl : lift (1 : WithConv (B →ₐ[k] B)).ofConv (AlgHom.id k B) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.lid k B).toAlgHom.comp
          (map (Bialgebra.counitAlgHom k B) (AlgHom.id k B)) := by
      refine Algebra.TensorProduct.ext' fun a b => ?_
      simp [AlgHom.convOne_apply, Algebra.smul_def]
    rw [hl, AlgHom.comp_apply] at h
    have := congrArg (Algebra.TensorProduct.lid k B).symm h
    rwa [AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, map_zero] at this
  counit_right := by
    have h := obsPt_one_right hx (AlgHom.id k B)
    rw [obsPt_eq_lift_obs] at h
    have hl : lift (AlgHom.id k B) (1 : WithConv (B →ₐ[k] B)).ofConv (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.rid k k B).toAlgHom.comp
          (map (AlgHom.id k B) (Bialgebra.counitAlgHom k B)) := by
      refine Algebra.TensorProduct.ext' fun a b => ?_
      simp [AlgHom.convOne_apply, Algebra.smul_def, mul_comm]
    rw [hl, AlgHom.comp_apply] at h
    have := congrArg (Algebra.TensorProduct.rid k k B).symm h
    rwa [AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, map_zero] at this

@[scoped simp] theorem obsCocycle_c {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B) :
    (obsCocycle k hx).c = obs k x := rfl

end ObsCocycle

section ExtAlg

open Algebra.TensorProduct

theorem map_comul_id_apply (z : B ⊗[k] B) :
    map (Bialgebra.comulAlgHom k B) (AlgHom.id k B) z = LinearMap.rTensor B (Coalgebra.comul (R := k)) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [LinearMap.rTensor_tmul]

theorem map_id_comul_apply (z : B ⊗[k] B) :
    map (AlgHom.id k B) (Bialgebra.comulAlgHom k B) z = LinearMap.lTensor B (Coalgebra.comul (R := k)) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [LinearMap.lTensor_tmul]

theorem assoc_apply_eq (z : (B ⊗[k] B) ⊗[k] B) :
    Algebra.TensorProduct.assoc k k k B B B z = TensorProduct.assoc k B B B z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    induction a with
    | zero => simp
    | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]
    | tmul c d => simp

variable {P : Type w} [CommRing P] [Algebra k P]

theorem assoc_map_map (f : B →ₐ[k] P) (z : (B ⊗[k] B) ⊗[k] B) :
    Algebra.TensorProduct.assoc k k k P P P (map (map f f) f z) =
      map f (map f f) (Algebra.TensorProduct.assoc k k k B B B z) := by
  have h : (Algebra.TensorProduct.assoc k k k P P P).toLinearMap ∘ₗ (map (map f f) f).toLinearMap =
      (map f (map f f)).toLinearMap ∘ₗ (Algebra.TensorProduct.assoc k k k B B B).toLinearMap :=
    TensorProduct.ext_threefold fun a b c => by simp
  first | exact LinearMap.congr_fun h z | simpa using LinearMap.congr_fun h z

variable (k B)

def ExtAlg (_γ : Cocycle₂ k B) : Type v := Polynomial B

variable {k B}

namespace ExtAlg

variable (γ : Cocycle₂ k B)

scoped instance instCommRing : CommRing (ExtAlg k B γ) := inferInstanceAs (CommRing (Polynomial B))
scoped instance instAlgebra : Algebra k (ExtAlg k B γ) := inferInstanceAs (Algebra k (Polynomial B))
scoped instance instAlgebraB : Algebra B (ExtAlg k B γ) := inferInstanceAs (Algebra B (Polynomial B))
scoped instance instIsScalarTower : IsScalarTower k B (ExtAlg k B γ) :=
  inferInstanceAs (IsScalarTower k B (Polynomial B))

def Cₐ : B →ₐ[k] ExtAlg k B γ := IsScalarTower.toAlgHom k B (ExtAlg k B γ)

def T : ExtAlg k B γ := (Polynomial.X : Polynomial B)

theorem Cₐ_apply (b : B) : Cₐ γ b = (Polynomial.C b : Polynomial B) := rfl

def liftAlg {S : Type*} [CommRing S] [Algebra k S] (f : B →ₐ[k] S) (s : S) : ExtAlg k B γ →ₐ[k] S :=
  Polynomial.aevalTower f s

@[scoped simp] theorem liftAlg_C {S : Type*} [CommRing S] [Algebra k S] (f : B →ₐ[k] S) (s : S) (b : B) :
    liftAlg γ f s (Cₐ γ b) = f b :=
  Polynomial.aevalTower_toAlgHom f s b

@[scoped simp] theorem liftAlg_T {S : Type*} [CommRing S] [Algebra k S] (f : B →ₐ[k] S) (s : S) :
    liftAlg γ f s (T γ) = s :=
  Polynomial.aevalTower_X f s

theorem algHom_ext {S : Type*} [Semiring S] [Algebra k S] {f g : ExtAlg k B γ →ₐ[k] S}
    (hC : ∀ b, f (Cₐ γ b) = g (Cₐ γ b)) (hT : f (T γ) = g (T γ)) : f = g :=
  Polynomial.algHom_ext' (AlgHom.ext hC) hT

def cT : ExtAlg k B γ ⊗[k] ExtAlg k B γ := map (Cₐ γ) (Cₐ γ) γ.c

def comul' : ExtAlg k B γ →ₐ[k] ExtAlg k B γ ⊗[k] ExtAlg k B γ :=
  liftAlg γ ((map (Cₐ γ) (Cₐ γ)).comp (Bialgebra.comulAlgHom k B)) (T γ ⊗ₜ[k] 1 + 1 ⊗ₜ[k] T γ + cT γ)

def counit' : ExtAlg k B γ →ₐ[k] k := liftAlg γ (Bialgebra.counitAlgHom k B) 0

@[scoped simp] theorem comul'_C (b : B) :
    comul' γ (Cₐ γ b) = map (Cₐ γ) (Cₐ γ) (Coalgebra.comul (R := k) b) := by
  rw [comul', liftAlg_C]; rfl

@[scoped simp] theorem comul'_T : comul' γ (T γ) = T γ ⊗ₜ[k] 1 + 1 ⊗ₜ[k] T γ + cT γ := by
  rw [comul', liftAlg_T]

@[scoped simp] theorem counit'_C (b : B) : counit' γ (Cₐ γ b) = Coalgebra.counit (R := k) b := by
  rw [counit', liftAlg_C]; rfl

@[scoped simp] theorem counit'_T : counit' γ (T γ) = 0 := by
  rw [counit', liftAlg_T]

theorem comul'_comp_C : (comul' γ).comp (Cₐ γ) = (map (Cₐ γ) (Cₐ γ)).comp (Bialgebra.comulAlgHom k B) :=
  AlgHom.ext fun b => comul'_C γ b

theorem counit'_comp_C : (counit' γ).comp (Cₐ γ) = Bialgebra.counitAlgHom k B :=
  AlgHom.ext fun b => counit'_C γ b

abbrev C3 : B ⊗[k] (B ⊗[k] B) →ₐ[k] ExtAlg k B γ ⊗[k] (ExtAlg k B γ ⊗[k] ExtAlg k B γ) :=
  map (Cₐ γ) (map (Cₐ γ) (Cₐ γ))

theorem map_comul'_id_map (z : B ⊗[k] B) :
    map (comul' γ) (AlgHom.id k (ExtAlg k B γ)) (map (Cₐ γ) (Cₐ γ) z) =
      map (map (Cₐ γ) (Cₐ γ)) (Cₐ γ) (map (Bialgebra.comulAlgHom k B) (AlgHom.id k B) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, comul'_comp_C, ← AlgHom.comp_apply,
    ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]

theorem map_id_comul'_map (z : B ⊗[k] B) :
    map (AlgHom.id k (ExtAlg k B γ)) (comul' γ) (map (Cₐ γ) (Cₐ γ) z) =
      C3 γ (map (AlgHom.id k B) (Bialgebra.comulAlgHom k B) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, comul'_comp_C, ← AlgHom.comp_apply,
    ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]

theorem coassoc_C (b : B) :
    Algebra.TensorProduct.assoc k k k _ _ _ (map (comul' γ) (AlgHom.id k _) (comul' γ (Cₐ γ b))) =
      map (AlgHom.id k _) (comul' γ) (comul' γ (Cₐ γ b)) := by
  rw [comul'_C, map_comul'_id_map, map_id_comul'_map, assoc_map_map, map_comul_id_apply, assoc_apply_eq,
    Coalgebra.coassoc_apply, map_id_comul_apply]

theorem coassoc_T :
    Algebra.TensorProduct.assoc k k k _ _ _ (map (comul' γ) (AlgHom.id k _) (comul' γ (T γ))) =
      map (AlgHom.id k _) (comul' γ) (comul' γ (T γ)) := by
  have hcoc := congrArg (C3 γ) γ.coc
  rw [map_add, map_add, ← assoc_map_map, ← assoc_map_map, map_tmul, map_one, map_tmul, map_one,
    ← map_comul'_id_map, ← map_id_comul'_map] at hcoc
  change Algebra.TensorProduct.assoc k k k _ _ _ (map (comul' γ) (AlgHom.id k _) (cT γ)) +
      Algebra.TensorProduct.assoc k k k _ _ _ (cT γ ⊗ₜ[k] 1) =
    map (AlgHom.id k _) (comul' γ) (cT γ) + 1 ⊗ₜ[k] cT γ at hcoc
  simp only [comul'_T, map_add, map_tmul, map_one, AlgHom.id_apply, TensorProduct.add_tmul,
    TensorProduct.tmul_add, Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_tmul]
  linear_combination hcoc

theorem counit_left_C (b : B) :
    map (counit' γ) (AlgHom.id k _) (comul' γ (Cₐ γ b)) =
      (Algebra.TensorProduct.lid k (ExtAlg k B γ)).symm (Cₐ γ b) := by
  rw [comul'_C, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, counit'_comp_C, AlgHom.id_comp]
  have h : map (Bialgebra.counitAlgHom k B) (Cₐ γ) (Coalgebra.comul (R := k) b) =
      map (AlgHom.id k k) (Cₐ γ) (LinearMap.rTensor B (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) b)) := by
    induction Coalgebra.comul (R := k) b with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c d => simp [LinearMap.rTensor_tmul]
  rw [h, Coalgebra.rTensor_counit_comul, map_tmul]
  rfl

theorem counit_left_T :
    map (counit' γ) (AlgHom.id k _) (comul' γ (T γ)) =
      (Algebra.TensorProduct.lid k (ExtAlg k B γ)).symm (T γ) := by
  have hc : map (counit' γ) (AlgHom.id k _) (cT γ) = 0 := by
    rw [cT, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, counit'_comp_C, AlgHom.id_comp]
    have h : map (Bialgebra.counitAlgHom k B) (Cₐ γ) γ.c =
        map (AlgHom.id k k) (Cₐ γ) (map (Bialgebra.counitAlgHom k B) (AlgHom.id k B) γ.c) := by
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
    rw [h, γ.counit_left, map_zero]
  simp only [comul'_T, map_add, map_tmul, counit'_T, map_one, AlgHom.id_apply, TensorProduct.zero_tmul,
    zero_add, hc, add_zero]
  rfl

theorem counit_right_C (b : B) :
    map (AlgHom.id k _) (counit' γ) (comul' γ (Cₐ γ b)) =
      (Algebra.TensorProduct.rid k k (ExtAlg k B γ)).symm (Cₐ γ b) := by
  rw [comul'_C, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, counit'_comp_C, AlgHom.id_comp]
  have h : map (Cₐ γ) (Bialgebra.counitAlgHom k B) (Coalgebra.comul (R := k) b) =
      map (Cₐ γ) (AlgHom.id k k) (LinearMap.lTensor B (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) b)) := by
    induction Coalgebra.comul (R := k) b with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c d => simp [LinearMap.lTensor_tmul]
  rw [h, Coalgebra.lTensor_counit_comul, map_tmul]
  rfl

theorem counit_right_T :
    map (AlgHom.id k _) (counit' γ) (comul' γ (T γ)) =
      (Algebra.TensorProduct.rid k k (ExtAlg k B γ)).symm (T γ) := by
  have hc : map (AlgHom.id k _) (counit' γ) (cT γ) = 0 := by
    rw [cT, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, counit'_comp_C, AlgHom.id_comp]
    have h : map (Cₐ γ) (Bialgebra.counitAlgHom k B) γ.c =
        map (Cₐ γ) (AlgHom.id k k) (map (AlgHom.id k B) (Bialgebra.counitAlgHom k B) γ.c) := by
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
    rw [h, γ.counit_right, map_zero]
  simp only [comul'_T, map_add, map_tmul, counit'_T, map_one, AlgHom.id_apply, TensorProduct.tmul_zero,
    add_zero, hc]
  rfl

scoped instance instBialgebra : Bialgebra k (ExtAlg k B γ) :=
  Bialgebra.ofAlgHom (comul' γ) (counit' γ)
    (algHom_ext γ (fun b => by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
        exact coassoc_C γ b)
      (by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
        exact coassoc_T γ))
    (algHom_ext γ (fun b => by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
        exact counit_left_C γ b)
      (by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
        exact counit_left_T γ))
    (algHom_ext γ (fun b => by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
        exact counit_right_C γ b)
      (by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
        exact counit_right_T γ))

theorem comul_def (f : ExtAlg k B γ) : Coalgebra.comul (R := k) f = comul' γ f := rfl

theorem counit_def (f : ExtAlg k B γ) : Coalgebra.counit (R := k) f = counit' γ f := rfl

theorem comul_T : Coalgebra.comul (R := k) (T γ) = T γ ⊗ₜ[k] 1 + 1 ⊗ₜ[k] T γ + cT γ := comul'_T γ

theorem counit_T : Coalgebra.counit (R := k) (T γ) = 0 := counit'_T γ

def Cb : B →ₐc[k] ExtAlg k B γ :=
  BialgHom.ofAlgHom (Cₐ γ) (counit'_comp_C γ) (comul'_comp_C γ).symm

@[scoped simp] theorem Cb_apply (b : B) : Cb γ b = Cₐ γ b := rfl

def coeff₀ : ExtAlg k B γ →ₗ[k] B := (Polynomial.lcoeff B 0).restrictScalars k

@[scoped simp] theorem coeff₀_C (b : B) : coeff₀ γ (Cₐ γ b) = b := Polynomial.coeff_C_zero

@[scoped simp] theorem coeff₀_T : coeff₀ γ (T γ) = 0 := Polynomial.coeff_X_zero

@[scoped simp] theorem coeff₀_one : coeff₀ γ 1 = 1 := Polynomial.coeff_one_zero

end ExtAlg
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg"

end ExtAlg
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg"

section KeyIdentity

variable (k : Type u) [CommRing k] {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable {B : Type v} [CommRing B] [Bialgebra k B]

open ExtAlg

def Xtilde {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B) :
    TruncatedWittVector p (m + 2) (ExtAlg k B (obsCocycle k hx)) :=
  zext (TruncWitt.map (Cb (obsCocycle k hx) : B →ₐ[k] ExtAlg k B (obsCocycle k hx)).toRingHom x) +
    top (T (obsCocycle k hx))

variable {k}

theorem obs_map_Cb {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B) :
    obs k (TruncWitt.map (Cb (obsCocycle k hx) : B →ₐ[k] ExtAlg k B (obsCocycle k hx)).toRingHom x) =
      cT (obsCocycle k hx) := by
  set γ := obsCocycle k hx
  have h1 : (Algebra.TensorProduct.includeLeft : ExtAlg k B γ →ₐ[k] ExtAlg k B γ ⊗[k] ExtAlg k B γ).comp
      (Cb γ : B →ₐ[k] ExtAlg k B γ) =
      (Algebra.TensorProduct.map (Cₐ γ) (Cₐ γ)).comp Algebra.TensorProduct.includeLeft :=
    AlgHom.ext fun b => rfl
  have h2 : (Algebra.TensorProduct.includeRight : ExtAlg k B γ →ₐ[k] ExtAlg k B γ ⊗[k] ExtAlg k B γ).comp
      (Cb γ : B →ₐ[k] ExtAlg k B γ) =
      (Algebra.TensorProduct.map (Cₐ γ) (Cₐ γ)).comp Algebra.TensorProduct.includeRight :=
    AlgHom.ext fun b => rfl
  rw [obs, obsPt_map, h1, h2, ← map_obsPt]
  rfl

theorem Xtilde_mem {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B) :
    Xtilde k hx ∈ wittHom k p (m + 2) (ExtAlg k B (obsCocycle k hx)) := by
  refine zext_add_top_mem_wittHom (map_mem_wittHom _ hx) ?_
  rw [comul_T, obs_map_Cb]

theorem coeff_Xtilde_last {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B) :
    (Xtilde k hx).coeff (Fin.last (m + 1)) = T (obsCocycle k hx) :=
  coeff_zext_add_top_last _ _

theorem coeff_Xtilde_castSucc {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (i : Fin (m + 1)) :
    (Xtilde k hx).coeff i.castSucc = Cₐ (obsCocycle k hx) (x.coeff i) := by
  rw [Xtilde, coeff_zext_add_top_castSucc, TruncWitt.coeff_map]
  rfl

theorem convPow_ofConv_comp {C D : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup D] [Module k D] [Coalgebra k D] (f : WithConv (D →ₗ[k] k)) (h : C →ₗc[k] D) (n : ℕ) :
    (f ^ n).ofConv ∘ₗ h.toLinearMap = ((WithConv.toConv (f.ofConv ∘ₗ h.toLinearMap)) ^ n).ofConv := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, LinearMap.convOne_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
      WithConv.ofConv_toConv, LinearMap.comp_assoc, CoalgHom.counit_comp]
  | succ n ih =>
    rw [pow_succ, pow_succ, LinearMap.convMul_comp_coalgHom_distrib, ih, WithConv.toConv_ofConv]

variable [CharP k p]

theorem key {x : TruncatedWittVector p (m + 1) B} (hx : x ∈ wittHom k p (m + 1) B)
    (β : WithConv (B →ₗ[k] k)) (hβ : β.ofConv 1 = 0) :
    LinearMap.mul' k k (TensorProduct.map (β ^ (p - 1)).ofConv β.ofConv (obs k x)) =
      (β.ofConv (x.coeff (Fin.last m))) ^ p := by
  set γ := obsCocycle k hx with hγ

  set βt : WithConv (ExtAlg k B γ →ₗ[k] k) := WithConv.toConv (β.ofConv ∘ₗ coeff₀ γ) with hβt
  have hcomp : βt.ofConv ∘ₗ (Cb γ).toLinearMap = β.ofConv := by
    refine LinearMap.ext fun b => ?_
    change β.ofConv (coeff₀ γ (Cₐ γ b)) = β.ofConv b
    rw [coeff₀_C]

  have V := (Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p (ExtAlg k B γ) k βt (Xtilde_mem hx)).2 m
    (by omega)
  have e1 : (Xtilde k hx).coeff ⟨m + 1, by omega⟩ = T γ := coeff_Xtilde_last hx
  have e2 : (Xtilde k hx).coeff ⟨m, by omega⟩ = Cₐ γ (x.coeff (Fin.last m)) := coeff_Xtilde_castSucc hx (Fin.last m)
  rw [e1, e2] at V
  have e3 : βt.ofConv (Cₐ γ (x.coeff (Fin.last m))) = β.ofConv (x.coeff (Fin.last m)) := by
    change β.ofConv (coeff₀ γ (Cₐ γ _)) = _
    rw [coeff₀_C]
  rw [e3] at V
  rw [← V]

  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.out.one_le).symm
  have hβT : βt.ofConv (T γ) = 0 := by
    change β.ofConv (coeff₀ γ (T γ)) = 0
    rw [coeff₀_T, map_zero]
  have hβ1 : βt.ofConv 1 = 0 := by
    change β.ofConv (coeff₀ γ 1) = 0
    rw [coeff₀_one, hβ]
  conv_rhs => rw [hp1, pow_succ, LinearMap.convMul_apply, comul_T]
  simp only [map_add, TensorProduct.map_tmul, LinearMap.mul'_apply, hβT, hβ1, mul_zero, zero_add]
  rw [cT]
  change _ = LinearMap.mul' k k (TensorProduct.map (βt ^ (p - 1)).ofConv βt.ofConv
    (TensorProduct.map (Cₐ γ).toLinearMap (Cₐ γ).toLinearMap γ.c))
  rw [← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp]
  change _ = LinearMap.mul' k k (TensorProduct.map ((βt ^ (p - 1)).ofConv ∘ₗ (Cb γ).toLinearMap)
    (βt.ofConv ∘ₗ (Cb γ).toLinearMap) (obs k x))
  rw [convPow_ofConv_comp, hcomp, WithConv.toConv_ofConv]

end KeyIdentity
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg"

end TensorForm
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg"

section CartierSide

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

open CartierDual

theorem toDual_pow (φ : CartierDual k A) (n : ℕ) :
    CartierDual.toDual k A (φ ^ n) = (WithConv.toConv (CartierDual.toDual k A φ) ^ n).ofConv := by
  induction n with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ n ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem convPow_apply (β : WithConv (A →ₗ[k] k)) (n : ℕ) (a : A) :
    (β ^ n).ofConv a = ((CartierDual.ofDual k A β.ofConv) ^ n) a := by
  have : (β ^ n).ofConv = CartierDual.toDual k A ((CartierDual.ofDual k A β.ofConv) ^ n) := by
    rw [toDual_pow, CartierDual.toDual_ofDual, WithConv.toConv_ofConv]
  rw [this]; rfl

theorem convPow_eq_zero {φ : CartierDual k A} {n : ℕ} (h : φ ^ n = 0) :
    (WithConv.toConv (CartierDual.toDual k A φ)) ^ n = 0 := by
  have : (WithConv.toConv (CartierDual.toDual k A φ) ^ n).ofConv = 0 := by
    refine LinearMap.ext fun a => ?_
    rw [convPow_apply, WithConv.ofConv_toConv, CartierDual.ofDual_toDual, h]
    rfl
  exact (WithConv.ofConv_injective this : _)

theorem tmul_ext {z : A ⊗[k] A}
    (h : ∀ φ ψ : Module.Dual k A, TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) z = 0) : z = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro F
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  change TensorProduct.dualDistrib k A A w z = 0
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | tmul φ ψ => exact h φ ψ

def pair (z : A ⊗[k] A) (r s : CartierDual k A) : k :=
  TensorProduct.dualDistrib k A A (CartierDual.toDual k A r ⊗ₜ[k] CartierDual.toDual k A s) z

@[scoped simp] theorem pair_tmul (a b : A) (r s : CartierDual k A) : pair (a ⊗ₜ[k] b) r s = r a * s b :=
  TensorProduct.dualDistrib_apply _ _ _ _

theorem pair_add (z z' : A ⊗[k] A) (r s : CartierDual k A) : pair (z + z') r s = pair z r s + pair z' r s := by
  unfold pair; rw [map_add]

theorem pair_zero (r s : CartierDual k A) : pair (0 : A ⊗[k] A) r s = 0 := by
  unfold pair; rw [map_zero]

theorem pair_add_left (z : A ⊗[k] A) (r r' s : CartierDual k A) : pair z (r + r') s = pair z r s + pair z r' s := by
  unfold pair; rw [map_add, TensorProduct.add_tmul, map_add, LinearMap.add_apply]

theorem pair_add_right (z : A ⊗[k] A) (r s s' : CartierDual k A) : pair z r (s + s') = pair z r s + pair z r s' := by
  unfold pair; rw [map_add, TensorProduct.tmul_add, map_add, LinearMap.add_apply]

theorem pair_smul_left (z : A ⊗[k] A) (c : k) (r s : CartierDual k A) : pair z (c • r) s = c * pair z r s := by
  unfold pair; rw [map_smul, ← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem pair_smul_right (z : A ⊗[k] A) (c : k) (r s : CartierDual k A) : pair z r (c • s) = c * pair z r s := by
  unfold pair; rw [map_smul, TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

def pairLin (z : A ⊗[k] A) : CartierDual k A →ₗ[k] CartierDual k A →ₗ[k] k :=
  LinearMap.mk₂ k (pair z) (pair_add_left z) (pair_smul_left z) (pair_add_right z) (pair_smul_right z)

@[scoped simp] theorem pairLin_apply (z : A ⊗[k] A) (r s : CartierDual k A) : pairLin z r s = pair z r s := rfl

theorem pair_comm (z : A ⊗[k] A) (r s : CartierDual k A) :
    pair (TensorProduct.comm k A A z) r s = pair z s r := by
  induction z with
  | zero => rw [map_zero, pair_zero, pair_zero]
  | add x y hx hy => rw [map_add, pair_add, pair_add, hx, hy]
  | tmul a b => rw [TensorProduct.comm_tmul, pair_tmul, pair_tmul, mul_comm]

theorem pair_one_left (z : A ⊗[k] A) (s : CartierDual k A) :
    pair z 1 s = s (Algebra.TensorProduct.lid k A
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k A) (AlgHom.id k A) z)) := by
  induction z with
  | zero => rw [pair_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => rw [pair_add, hx, hy, map_add, map_add, map_add]
  | tmul a b =>
    rw [pair_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.counitAlgHom_apply,
      Algebra.TensorProduct.lid_tmul, map_smul, smul_eq_mul, CartierDual.one_apply]

def pair₃ (r s t : CartierDual k A) : A ⊗[k] (A ⊗[k] A) →ₗ[k] k :=
  TensorProduct.dualDistrib k A (A ⊗[k] A)
    (CartierDual.toDual k A r ⊗ₜ[k] TensorProduct.dualDistrib k A A
      (CartierDual.toDual k A s ⊗ₜ[k] CartierDual.toDual k A t))

@[scoped simp] theorem pair₃_tmul (r s t : CartierDual k A) (a b c : A) :
    pair₃ r s t (a ⊗ₜ[k] (b ⊗ₜ[k] c)) = r a * (s b * t c) := by
  rw [pair₃, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]; rfl

theorem pair_comul_left (a b : A) (r s t : CartierDual k A) :
    pair₃ r s t (Algebra.TensorProduct.assoc k k k A A A
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k A) (AlgHom.id k A) (a ⊗ₜ[k] b))) =
      (r * s) a * t b := by
  rw [Algebra.TensorProduct.map_tmul, Bialgebra.comulAlgHom_apply, AlgHom.id_apply, CartierDual.mul_apply,
    ← (Coalgebra.Repr.arbitrary k a).eq]
  simp only [map_sum, TensorProduct.sum_tmul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.assoc_tmul, pair₃_tmul, TensorProduct.dualDistrib_apply, mul_assoc]
  rfl

theorem pair₃_assoc_map_comul (z : A ⊗[k] A) (r s t : CartierDual k A) :
    pair₃ r s t (Algebra.TensorProduct.assoc k k k A A A
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k A) (AlgHom.id k A) z)) = pair z (r * s) t := by
  induction z with
  | zero => rw [map_zero, map_zero, map_zero, pair_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, pair_add]
  | tmul a b => rw [pair_comul_left, pair_tmul]

theorem pair₃_assoc_tmul_one (z : A ⊗[k] A) (r s t : CartierDual k A) :
    pair₃ r s t (Algebra.TensorProduct.assoc k k k A A A (z ⊗ₜ[k] (1 : A))) = pair z r s * t 1 := by
  induction z with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, pair_zero, zero_mul]
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy, pair_add, add_mul]
  | tmul a b => rw [Algebra.TensorProduct.assoc_tmul, pair₃_tmul, pair_tmul, mul_assoc]

theorem pair₃_map_id_comul (z : A ⊗[k] A) (r s t : CartierDual k A) :
    pair₃ r s t (Algebra.TensorProduct.map (AlgHom.id k A) (Bialgebra.comulAlgHom k A) z) = pair z r (s * t) := by
  induction z with
  | zero => rw [map_zero, map_zero, pair_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, pair_add]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, Bialgebra.comulAlgHom_apply, AlgHom.id_apply, pair_tmul,
      CartierDual.mul_apply, ← (Coalgebra.Repr.arbitrary k b).eq]
    simp only [map_sum, TensorProduct.tmul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair₃_tmul, TensorProduct.dualDistrib_apply]
    rfl

theorem pair₃_one_tmul (z : A ⊗[k] A) (r s t : CartierDual k A) :
    pair₃ r s t ((1 : A) ⊗ₜ[k] z) = r 1 * pair z s t := by
  induction z with
  | zero => rw [TensorProduct.tmul_zero, map_zero, pair_zero, mul_zero]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, pair_add, mul_add]
  | tmul a b => rw [pair₃_tmul, pair_tmul]

variable {m : ℕ} {x : TruncatedWittVector p (m + 1) A} (hx : x ∈ wittHom k p (m + 1) A)
include hx

theorem pair_obs_symm (r s : CartierDual k A) : pair (obs k x) r s = pair (obs k x) s r := by
  have h := obsPt_comm hx (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A)
    (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A)
  have hl : Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A)
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.comm k A A).toAlgHom := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [obsPt_eq_lift_obs, hl] at h
  change (Algebra.TensorProduct.comm k A A) (obs k x) = obs k x at h
  have h' : (TensorProduct.comm k A A) (obs k x) = obs k x := h
  rw [← pair_comm (obs k x) s r, h']

theorem pair_obs_cocycle (r s t : CartierDual k A) :
    pair (obs k x) (r * s) t + pair (obs k x) r s * Coalgebra.counit (R := k) t =
      pair (obs k x) r (s * t) + Coalgebra.counit (R := k) r * pair (obs k x) s t := by
  have h := congrArg (pair₃ r s t) (obsCocycle k hx).coc
  rw [map_add, map_add, obsCocycle_c, pair₃_assoc_map_comul, pair₃_assoc_tmul_one, pair₃_map_id_comul,
    pair₃_one_tmul] at h
  rw [CartierDual.counit_apply, CartierDual.counit_apply]
  exact h

theorem pair_obs_one_left (s : CartierDual k A) : pair (obs k x) 1 s = 0 := by
  rw [pair_one_left, ← obsCocycle_c k hx, (obsCocycle k hx).counit_left, map_zero, map_zero]

theorem pair_obs_pow (r : CartierDual k A) (hr : Coalgebra.counit (R := k) r = 0) :
    pair (obs k x) (r ^ (p - 1)) r = (r (x.coeff (Fin.last m))) ^ p := by
  have h := key hx (WithConv.toConv (CartierDual.toDual k A r)) (by rw [CartierDual.counit_apply] at hr; exact hr)
  rw [WithConv.ofConv_toConv, ← toDual_pow, CartierDual.toDual_apply] at h
  rw [← h, pair, CartierDual.dualDistrib_tmul_eq_mul'_comp_map, LinearMap.comp_apply]

variable [PerfectField k]
variable (hlast : ∀ β : WithConv (A →ₗ[k] k), β ^ p = 0 → β.ofConv (x.coeff (Fin.last m)) = 0)
include hlast

theorem exists_comul_eq :
    ∃ u : A, Coalgebra.comul (R := k) u = u ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u + obs k x := by

  let ℓ : CartierDual k A →ₗ[k] k :=
    { toFun := fun r => r (x.coeff (Fin.last m))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hℓ_apply : ∀ r, ℓ r = r (x.coeff (Fin.last m)) := fun r => rfl
  obtain ⟨u, hu⟩ :=
    HopfAlgebra.exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow k p
      (CartierDual k A) (pairLin (obs k x))
      (fun r s => pair_obs_symm hx r s)
      (fun r s t => pair_obs_cocycle hx r s t)
      (fun s => pair_obs_one_left hx s)
      ℓ
      (by rw [hℓ_apply, CartierDual.one_apply]; exact counit_coeff_of_mem_wittHom hx _)
      (fun r hr => by
        rw [hℓ_apply]
        exact hlast (WithConv.toConv (CartierDual.toDual k A r)) (convPow_eq_zero hr))
      (fun r hr => by rw [pairLin_apply, hℓ_apply]; exact pair_obs_pow hx r hr)
  set u' := (Module.evalEquiv k A).symm (u ∘ₗ (CartierDual.ofDual k A).toLinearMap) with hu'
  refine ⟨u', ?_⟩
  have happ : ∀ r : CartierDual k A, r u' = u r := fun r =>
    Module.apply_evalEquiv_symm_apply k A (CartierDual.toDual k A r) (u ∘ₗ (CartierDual.ofDual k A).toLinearMap)
  rw [← sub_eq_zero]
  refine tmul_ext fun φ ψ => ?_
  have h1 : TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) (Coalgebra.comul (R := k) u') =
      (CartierDual.ofDual k A φ * CartierDual.ofDual k A ψ) u' := by
    rw [CartierDual.mul_apply]; rfl
  have h2 : TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) (obs k x) =
      pair (obs k x) (CartierDual.ofDual k A φ) (CartierDual.ofDual k A ψ) := rfl
  have e1 : φ u' = u (CartierDual.ofDual k A φ) := happ _
  have e2 : ψ u' = u (CartierDual.ofDual k A ψ) := happ _
  rw [map_sub, map_add, map_add, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply, h1, h2, happ,
    hu, pairLin_apply, CartierDual.counit_apply, CartierDual.counit_apply, e1, e2, CartierDual.ofDual_apply,
    CartierDual.ofDual_apply]
  ring

theorem exists_extension :
    ∃ y : TruncatedWittVector p (m + 2) A,
      y ∈ wittHom k p (m + 2) A ∧ TruncatedWittVector.truncate (Nat.le_succ (m + 1)) y = x := by
  obtain ⟨u, hu⟩ := exists_comul_eq hx hlast
  exact ⟨zext x + top u, zext_add_top_mem_wittHom hx hu, truncate_zext_add_top x u⟩

end CartierSide
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg"

end Deformation.WittVMStep
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep"
p2m_reactivate "P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation.WittVMStep.ExtAlg P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.Deformation"

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (m : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (x : TruncatedWittVector p (m + 1) A) (hx : x ∈ Deformation.wittHom k p (m + 1) A)
    (hlast : ∀ β : WithConv (A →ₗ[k] k), β ^ p = 0 → β.ofConv (x.coeff (Fin.last m)) = 0) :
    ∃ y : TruncatedWittVector p (m + 2) A,
      y ∈ Deformation.wittHom k p (m + 2) A ∧
        TruncatedWittVector.truncate (Nat.le_succ (m + 1)) y = x :=
  Deformation.WittVMStep.exists_extension hx hlast

end
end S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero
end P2MW
export P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero (solution)
