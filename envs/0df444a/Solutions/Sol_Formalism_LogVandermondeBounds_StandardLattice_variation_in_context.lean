-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.variation_in_context
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:07.764031+00:00
-- url     : https://prove2.me/submissions/5599e116-994f-4e80-bd09-8de6fb7faf57

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_variation_exponent_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : LogVandermondeVariationOfLogLe := by
  intro n Δ u u' hw hΔ
  have h := variation_exponent_bound n Δ u u' hw
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have : 0 ≤ ((n : ℝ) + 2) * Real.log ((n : ℝ) + 2) := by positivity
  nlinarith
end Formalism.LogVandermondeBounds.StandardLattice
