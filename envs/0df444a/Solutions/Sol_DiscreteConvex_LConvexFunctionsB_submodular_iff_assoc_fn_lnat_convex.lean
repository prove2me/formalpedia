-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.submodular_iff_assoc_fn_lnat_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:38:43.810822+00:00
-- url     : https://prove2.me/submissions/e1d9a7d1-323f-4480-8782-8b040ef05fb6

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_Submodular
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_AssocFn

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical in
open scoped Pointwise in
lemma DiscreteConvex.LConvexFunctionsB.p923_indicatorVec_injective
    {V : Type*} [Fintype V] [DecidableEq V] {X Y : Finset V}
    (h : DiscreteConvex.LConvexFunctionsB.IndicatorVec X =
      DiscreteConvex.LConvexFunctionsB.IndicatorVec Y) : X = Y := by
  ext v
  have := congrFun h v
  simp only [DiscreteConvex.LConvexFunctionsB.IndicatorVec] at this
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp_all

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma p923_assocFn_ind (rho : Finset V → WithTop ℝ) (X : Finset V) :
    AssocFn rho (IndicatorVec X) = rho X := by
  have h : ∃ Y : Finset V, IndicatorVec X = IndicatorVec Y := ⟨X, rfl⟩
  unfold AssocFn
  rw [dif_pos h]
  congr 1
  exact (p923_indicatorVec_injective h.choose_spec).symm

lemma p923_assocFn_top (rho : Finset V → WithTop ℝ) (p : V → ℤ)
    (hp : ¬ ∃ X : Finset V, p = IndicatorVec X) : AssocFn rho p = ⊤ := by
  unfold AssocFn
  rw [dif_neg hp]

/-- lift of a set to `Option V → ℤ` with zero at `none`. -/
def p923_lift (X : Finset V) : Option V → ℤ := fun o => o.elim 0 (IndicatorVec X)

lemma p923_lifted_lift (g : (V → ℤ) → WithTop ℝ) (X : Finset V) :
    LiftedFunctionL g (p923_lift X) = g (IndicatorVec X) := by
  unfold LiftedFunctionL
  congr 1
  funext v
  simp [p923_lift]

lemma p923_lift_sup (X Y : Finset V) : p923_lift X ⊔ p923_lift Y = p923_lift (X ∪ Y) := by
  funext o
  cases o with
  | none => simp [p923_lift]
  | some v =>
    simp only [Pi.sup_apply, p923_lift, Option.elim, IndicatorVec, Finset.mem_union]
    by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]

lemma p923_lift_inf (X Y : Finset V) : p923_lift X ⊓ p923_lift Y = p923_lift (X ∩ Y) := by
  funext o
  cases o with
  | none => simp [p923_lift]
  | some v =>
    simp only [Pi.inf_apply, p923_lift, Option.elim, IndicatorVec, Finset.mem_inter]
    by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]

lemma p923_ind_le_one (X : Finset V) (v : V) : IndicatorVec X v ≤ 1 := by
  unfold IndicatorVec; split_ifs <;> norm_num

lemma p923_ind_nonneg (X : Finset V) (v : V) : 0 ≤ IndicatorVec X v := by
  unfold IndicatorVec; split_ifs <;> norm_num

lemma p923_le_of_lt (p q : Option V → ℤ) (X Y : Finset V)
    (hX : (fun v => p (some v) - p none) = IndicatorVec X)
    (hY : (fun v => q (some v) - q none) = IndicatorVec Y)
    (hlt : p none < q none) : p ≤ q := by
  intro o
  cases o with
  | none => exact hlt.le
  | some v =>
    have h1 := congrFun hX v
    have h2 := congrFun hY v
    beta_reduce at h1 h2
    have := p923_ind_le_one X v
    have := p923_ind_nonneg Y v
    show p (some v) ≤ q (some v)
    omega

lemma p923_sbf (rho : Finset V → WithTop ℝ) (hsub : Submodular rho) :
    SBF (LiftedFunctionL (AssocFn rho)) := by
  intro p q
  by_cases hp : ∃ X : Finset V, (fun v => p (some v) - p none) = IndicatorVec X
  swap
  · have : LiftedFunctionL (AssocFn rho) p = ⊤ := p923_assocFn_top rho _ hp
    rw [this, top_add]; exact le_top
  by_cases hq : ∃ X : Finset V, (fun v => q (some v) - q none) = IndicatorVec X
  swap
  · have : LiftedFunctionL (AssocFn rho) q = ⊤ := p923_assocFn_top rho _ hq
    rw [this, add_top]; exact le_top
  obtain ⟨X, hX⟩ := hp
  obtain ⟨Y, hY⟩ := hq
  rcases lt_trichotomy (p none) (q none) with hlt | heq | hgt
  · have hle := p923_le_of_lt p q X Y hX hY hlt
    rw [sup_eq_right.mpr hle, inf_eq_left.mpr hle, add_comm]
  · have hs : (fun v => (p ⊔ q) (some v) - (p ⊔ q) none) = IndicatorVec (X ∪ Y) := by
      funext v
      have h1 := congrFun hX v
      have h2 := congrFun hY v
      beta_reduce at h1 h2
      simp only [Pi.sup_apply, IndicatorVec, Finset.mem_union] at h1 h2 ⊢
      by_cases a : v ∈ X <;> by_cases b : v ∈ Y <;> simp only [a, b, if_true, if_false] at h1 h2 ⊢ <;>
        simp <;> omega
    have hi : (fun v => (p ⊓ q) (some v) - (p ⊓ q) none) = IndicatorVec (X ∩ Y) := by
      funext v
      have h1 := congrFun hX v
      have h2 := congrFun hY v
      beta_reduce at h1 h2
      simp only [Pi.inf_apply, IndicatorVec, Finset.mem_inter] at h1 h2 ⊢
      by_cases a : v ∈ X <;> by_cases b : v ∈ Y <;> simp only [a, b, if_true, if_false] at h1 h2 ⊢ <;>
        simp <;> omega
    have ep : LiftedFunctionL (AssocFn rho) p = rho X := by
      show AssocFn rho _ = _; rw [hX, p923_assocFn_ind]
    have eq' : LiftedFunctionL (AssocFn rho) q = rho Y := by
      show AssocFn rho _ = _; rw [hY, p923_assocFn_ind]
    have es : LiftedFunctionL (AssocFn rho) (p ⊔ q) = rho (X ∪ Y) := by
      show AssocFn rho _ = _; rw [hs, p923_assocFn_ind]
    have ei : LiftedFunctionL (AssocFn rho) (p ⊓ q) = rho (X ∩ Y) := by
      show AssocFn rho _ = _; rw [hi, p923_assocFn_ind]
    rw [ep, eq', es, ei]
    exact hsub X Y
  · have hle := p923_le_of_lt q p Y X hY hX hgt
    rw [sup_eq_left.mpr hle, inf_eq_right.mpr hle]

lemma p923_trf (g : (V → ℤ) → WithTop ℝ) : TRF (LiftedFunctionL g) := by
  refine ⟨0, fun p => ?_⟩
  simp only [WithTop.coe_zero, add_zero]
  unfold LiftedFunctionL
  congr 1
  funext v
  simp only [Pi.add_apply, Pi.one_apply]
  ring

end DiscreteConvex.LConvexFunctionsB

open Classical DiscreteConvex.LConvexFunctionsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (rho : Finset V → WithTop ℝ)
    (hdom : ∃ X, rho X ≠ ⊤) :
    Submodular rho ↔ LNaturalConvex (AssocFn rho) := by
  constructor
  · intro h
    exact ⟨p923_sbf rho h, p923_trf _⟩
  · rintro ⟨hs, -⟩ X Y
    have := hs (p923_lift X) (p923_lift Y)
    rw [p923_lift_sup, p923_lift_inf, p923_lifted_lift, p923_lifted_lift, p923_lifted_lift,
      p923_lifted_lift, p923_assocFn_ind, p923_assocFn_ind, p923_assocFn_ind,
      p923_assocFn_ind] at this
    exact this
