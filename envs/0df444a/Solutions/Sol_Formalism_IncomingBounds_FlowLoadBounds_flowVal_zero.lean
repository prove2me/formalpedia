-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.flowVal_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:08.566538+00:00
-- url     : https://prove2.me/submissions/255c6a07-9679-4042-b6f0-9cd40916765a

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
theorem _root_.solution : flowVal d (0 : ZMod d → ℕ → ℝ) = 0 := by simp [Formalism.IncomingBounds.flowVal]
end Formalism.IncomingBounds.FlowLoadBounds
