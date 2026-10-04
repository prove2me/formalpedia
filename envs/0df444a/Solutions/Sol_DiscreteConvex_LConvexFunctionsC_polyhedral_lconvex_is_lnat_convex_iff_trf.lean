-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_is_lnat_convex_iff_trf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:05:31.48375+00:00
-- url     : https://prove2.me/submissions/3a3be425-d116-4c2e-a10a-896cd7ae3e28

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR

set_option autoImplicit false

namespace P71fc9957

open DiscreteConvex.LConvexFunctionsC

lemma lift_sbf_aux {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hS : SBFR g) (r : ℝ)
    (hT : ∀ p : V → ℝ, ∀ alpha : ℝ, g (fun v => p v + alpha) = g p + (((alpha * r : ℝ)) : WithTop ℝ))
    (x y : Option V → ℝ) (hab : x none ≤ y none) :
    LiftedFunctionLR g x + LiftedFunctionLR g y ≥
      LiftedFunctionLR g (x ⊔ y) + LiftedFunctionLR g (x ⊓ y) := by
  have h1 : LiftedFunctionLR g x
      = g (fun v => x (some v) - y none) + (((y none - x none) * r : ℝ) : WithTop ℝ) := by
    rw [← hT]
    unfold LiftedFunctionLR
    congr 1
    funext v
    ring
  have h2 : LiftedFunctionLR g y = g (fun v => y (some v) - y none) := rfl
  have h3 : LiftedFunctionLR g (x ⊔ y)
      = g ((fun v => x (some v) - y none) ⊔ (fun v => y (some v) - y none)) := by
    unfold LiftedFunctionLR
    congr 1
    funext v
    simp only [Pi.sup_apply]
    rw [sup_eq_right.mpr hab]
    exact (max_sub_sub_right _ _ _).symm
  have h4 : LiftedFunctionLR g (x ⊓ y)
      = g ((fun v => x (some v) - y none) ⊓ (fun v => y (some v) - y none))
        + (((y none - x none) * r : ℝ) : WithTop ℝ) := by
    rw [← hT]
    unfold LiftedFunctionLR
    congr 1
    funext v
    simp only [Pi.inf_apply]
    rw [inf_eq_left.mpr hab]
    rcases le_total (x (some v)) (y (some v)) with h | h
    · rw [inf_eq_left.mpr h,
        inf_eq_left.mpr (by linarith : x (some v) - y none ≤ y (some v) - y none)]
      ring
    · rw [inf_eq_right.mpr h,
        inf_eq_right.mpr (by linarith : y (some v) - y none ≤ x (some v) - y none)]
      ring
  rw [h1, h2, h3, h4]
  have hs := hS (fun v => x (some v) - y none) (fun v => y (some v) - y none)
  set A := g (fun v => x (some v) - y none)
  set B := g (fun v => y (some v) - y none)
  set C := g ((fun v => x (some v) - y none) ⊔ (fun v => y (some v) - y none))
  set D := g ((fun v => x (some v) - y none) ⊓ (fun v => y (some v) - y none))
  set E : WithTop ℝ := (((y none - x none) * r : ℝ) : WithTop ℝ)
  have : A + E + B = (A + B) + E := by rw [add_right_comm]
  have h' : C + (D + E) = (C + D) + E := by rw [add_assoc]
  show C + (D + E) ≤ A + E + B
  rw [this, h']
  exact add_le_add hs (le_refl E)

lemma lift_sbf {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hS : SBFR g) (hT : TRFR g) :
    SBFR (LiftedFunctionLR g) := by
  obtain ⟨r, hr⟩ := hT
  have hr' : ∀ p : V → ℝ, ∀ alpha : ℝ,
      g (fun v => p v + alpha) = g p + (((alpha * r : ℝ)) : WithTop ℝ) := by
    intro p alpha
    rw [hr p alpha]
    norm_cast
  intro x y
  rcases le_total (x none) (y none) with hab | hab
  · exact lift_sbf_aux g hS r hr' x y hab
  · have := lift_sbf_aux g hS r hr' y x hab
    rw [sup_comm, inf_comm, add_comm (LiftedFunctionLR g x)]
    exact this

lemma lift_trf {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) : TRFR (LiftedFunctionLR g) := by
  refine ⟨0, fun x alpha => ?_⟩
  rw [WithTop.coe_zero, mul_zero, add_zero]
  unfold LiftedFunctionLR
  congr 1
  funext v
  ring

lemma sbf_of_lift {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (h : SBFR (LiftedFunctionLR g)) : SBFR g := by
  intro p q
  have := h (fun o => Option.elim o 0 p) (fun o => Option.elim o 0 q)
  unfold LiftedFunctionLR at this
  have e1 : (fun v => (fun o => Option.elim o 0 p : Option V → ℝ) (some v)
      - (fun o => Option.elim o 0 p : Option V → ℝ) none) = p := by
    funext v; simp
  have e2 : (fun v => (fun o => Option.elim o 0 q : Option V → ℝ) (some v)
      - (fun o => Option.elim o 0 q : Option V → ℝ) none) = q := by
    funext v; simp
  have e3 : (fun v => ((fun o => Option.elim o 0 p) ⊔ (fun o => Option.elim o 0 q) : Option V → ℝ) (some v)
      - ((fun o => Option.elim o 0 p) ⊔ (fun o => Option.elim o 0 q) : Option V → ℝ) none) = p ⊔ q := by
    funext v; simp
  have e4 : (fun v => ((fun o => Option.elim o 0 p) ⊓ (fun o => Option.elim o 0 q) : Option V → ℝ) (some v)
      - ((fun o => Option.elim o 0 p) ⊓ (fun o => Option.elim o 0 q) : Option V → ℝ) none) = p ⊓ q := by
    funext v; simp
  rw [e1, e2, e3, e4] at this
  exact this

end P71fc9957

open Classical in
open scoped Pointwise in
open DiscreteConvex.LConvexFunctionsC in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ) :
    ((SBFR g ∧ TRFR g) → LNaturalConvexR g) ∧ (LNaturalConvexR g → (TRFR g → SBFR g)) := by
  refine ⟨fun h => ⟨P71fc9957.lift_sbf g h.1 h.2, P71fc9957.lift_trf g⟩, fun h _ => ?_⟩
  exact P71fc9957.sbf_of_lift g h.1
