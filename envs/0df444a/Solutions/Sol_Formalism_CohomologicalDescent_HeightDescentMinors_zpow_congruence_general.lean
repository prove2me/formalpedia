-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.zpow_congruence_general
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:34.303496+00:00
-- url     : https://prove2.me/submissions/439b34bd-96e2-464e-8c0f-ce9cdeed7a8c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_sq_dvd_one_add_pow_sub_linear

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : ZpowCongGen := by
  intro R _ x v U κ hU
  obtain ⟨n, rfl | rfl⟩ := κ.eq_nat_or_neg
  · have := sq_dvd_one_add_pow_sub_linear R x v n
    simpa [zpow_natCast, hU] using this
  · obtain ⟨s, hs⟩ := sq_dvd_one_add_pow_sub_linear R x v n
    have h1 : ((U ^ n : Rˣ) : R) * ((U ^ (-(n : ℤ)) : Rˣ) : R) = 1 := by
      rw [← Units.val_mul]; simp
    have h2 : ((U ^ n : Rˣ) : R) = 1 + (n : R) * (x * v) + x ^ 2 * s := by
      rw [Units.val_pow_eq_pow_val, hU]; linear_combination hs
    have h3 : x ^ 2 ∣ ((U ^ n : Rˣ) : R) *
        (((U ^ (-(n : ℤ)) : Rˣ) : R) - (1 + ((-(n : ℤ) : ℤ) : R) * (x * v))) := by
      refine ⟨(n : R) ^ 2 * v ^ 2 - s * (1 - n * (x * v)), ?_⟩
      rw [mul_sub, h1, h2]; push_cast; ring
    exact Units.dvd_mul_left.mp h3
end Formalism.CohomologicalDescent.HeightDescentMinors
