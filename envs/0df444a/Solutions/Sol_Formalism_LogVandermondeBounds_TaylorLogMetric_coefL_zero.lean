-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.TaylorLogMetric.coefL_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:46.133472+00:00
-- url     : https://prove2.me/submissions/a6dd3893-6b8f-4e50-bfc2-93163b2882b0

import Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric

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
theorem _root_.solution (p a : ℕ) (h : ¬∃ j, a = (p ^ 2) ^ j) : coefL p a = 0 := by
  unfold coefL
  rw [dif_neg h]
end Formalism.LogVandermondeBounds.TaylorLogMetric
