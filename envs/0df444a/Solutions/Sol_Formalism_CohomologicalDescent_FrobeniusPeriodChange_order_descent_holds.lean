-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.order_descent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:21.653167+00:00
-- url     : https://prove2.me/submissions/6ff1848e-2d0c-4dc1-b470-9cf6d9c7ecc8

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_linear_division_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : OrderDescent := by
  intro O _ _ I _ x L _ _ em jj hx hem hC hX S
  obtain ⟨w, hw⟩ := hX
  have hj : jj (X - C x) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  induction S with
  | zero => intro m _; simp
  | succ S ih =>
    intro m hm
    obtain ⟨f₁, a, rfl⟩ := (linear_division_holds O I x hx).1 m
    have h1 : (X : L⟦X⟧) ∣ jj ((X - C x) * f₁ + C a) :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero S)) hm
    rw [map_add, map_mul, hj, hC] at h1
    have h2 : (X : L⟦X⟧) ∣ C (em a) :=
      (dvd_add_right ((dvd_mul_right _ _).mul_right _)).1 h1
    have h3 : em a = 0 := by
      have := PowerSeries.X_dvd_iff.1 h2
      simpa using this
    have h4 : a = 0 := hem (by simpa using h3)
    subst h4
    rw [map_add, map_mul, hj, map_zero, map_zero, add_zero, pow_succ', mul_assoc] at hm
    have h5 : (X : L⟦X⟧) ^ S ∣ ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * jj f₁ :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 hm
    rw [Units.dvd_mul_left] at h5
    rw [map_zero, add_zero, pow_succ']
    exact mul_dvd_mul_left _ (ih f₁ h5)
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
