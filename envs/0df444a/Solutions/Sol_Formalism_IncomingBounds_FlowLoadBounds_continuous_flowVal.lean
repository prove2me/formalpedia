-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.continuous_flowVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.976944+00:00
-- url     : https://prove2.me/submissions/e988082e-8541-4415-8c3b-4145872b7838

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution : Continuous fun x : ZMod d → ℕ → ℝ => flowVal d x := by
  unfold Formalism.IncomingBounds.flowVal
  fun_prop
end Formalism.IncomingBounds.FlowLoadBounds
