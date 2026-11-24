-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.TaylorLogMetric.coefL_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:45.372587+00:00
-- url     : https://prove2.me/submissions/63596e1b-5fcc-4e30-b849-7c9aea01261e

import Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_sq_ge_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.TaylorLogMetric
open Finset
namespace Formalism.LogVandermondeBounds.TaylorLogMetric
theorem _root_.solution (p j : ℕ) (hp : 2 ≤ p) : coefL p ((p ^ 2) ^ j) = 1 / (p : ℚ) ^ j := by
  have h : ∃ j', (p ^ 2) ^ j = (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefL
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) (Classical.choose_spec h)
  rw [← hj]
end Formalism.LogVandermondeBounds.TaylorLogMetric
