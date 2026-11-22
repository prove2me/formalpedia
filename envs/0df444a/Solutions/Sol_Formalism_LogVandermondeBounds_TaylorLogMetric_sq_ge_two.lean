-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.TaylorLogMetric.sq_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:33.945821+00:00
-- url     : https://prove2.me/submissions/94575f1a-977d-4e68-a268-1c032f813a2c

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
theorem _root_.solution (p : ℕ) (hp : 2 ≤ p) : 2 ≤ p ^ 2 := by nlinarith
end Formalism.LogVandermondeBounds.TaylorLogMetric
