-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.coeff_subst_X_mul_of_low_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:20.081901+00:00
-- url     : https://prove2.me/submissions/ff06b5f0-daab-4751-8f4e-211d40c266ba

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_eq_sum_range_add_pow_mul

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
theorem _root_.solution (s f : R⟦X⟧) (j : ℕ) (hj : 0 < j)
    (h0 : ∀ i, 0 < i → i < j → coeff i f = 0) :
    coeff j (f.subst (X * s)) = coeff j f * constantCoeff s ^ j := by
  have ha : HasSubst (X * s) := HasSubst.of_constantCoeff_zero' (by simp)
  obtain ⟨h, hh⟩ := subst_eq_sum_range_add_pow_mul ha (j + 1) f
  rw [hh, map_add, map_sum]
  have e1 : coeff j ((X * s) ^ (j + 1) * h) = 0 := by
    rw [mul_pow, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  rw [e1, add_zero, Finset.sum_eq_single j]
  · rw [coeff_C_mul, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_pow]
  · intro k hk hkj
    rw [coeff_C_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, coeff_one, if_neg hj.ne', mul_zero]
    · rw [h0 k hk0 (by have := Finset.mem_range.mp hk; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self j)) h
end Formalism.CohomologicalDescent.HeightDescentMinors
