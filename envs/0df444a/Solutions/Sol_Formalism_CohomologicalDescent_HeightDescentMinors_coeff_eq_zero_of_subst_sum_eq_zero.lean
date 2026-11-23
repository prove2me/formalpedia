-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.coeff_eq_zero_of_subst_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:51.070394+00:00
-- url     : https://prove2.me/submissions/f29a3e4b-2d2c-4aef-990e-8ecdaeaa6011

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_cancel_unit_mul_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_eq_zero_of_sum_subst

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (k : ℕ) :
    ∀ d : Fin n → R⟦X⟧, ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0 →
      ∀ j, coeff k (d j) = 0 := by
  have hP := hasSubst_unit_mul_X_pow n hn w
  induction k with
  | zero =>
    intro d h0 j
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_eq_zero_of_sum_subst n hn w d h0 j
  | succ k ih =>
    intro d h0 j
    have hc := constantCoeff_eq_zero_of_sum_subst n hn w d h0
    have hd : ∀ j, d j = X * PowerSeries.mk fun p => coeff (p + 1) (d j) := by
      intro j
      conv_lhs => rw [eq_X_mul_shift_add_const (d j), hc j, map_zero, add_zero]
    have h1 : (w : R⟦X⟧) * X ^ n * ∑ j : Fin n, (PowerSeries.mk fun p => coeff (p + 1) (d j)).subst
        ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = (w : R⟦X⟧) * X ^ n * 0 := by
      rw [mul_zero, ← h0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_rhs => rw [hd j, subst_mul hP, subst_X hP]
      ring
    have h2 := ih (fun j => PowerSeries.mk fun p => coeff (p + 1) (d j)) (cancel_unit_mul_X_pow n w h1) j
    simpa using h2
end Formalism.CohomologicalDescent.HeightDescentMinors
