-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.continuous_load
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:56.88704+00:00
-- url     : https://prove2.me/submissions/c593974e-9068-45b7-b068-7ecc99161b08

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
theorem _root_.solution (s : ZMod d) : Continuous fun x : ZMod d → ℕ → ℝ => dpLoad l d x s := by
  unfold dpLoad
  fun_prop
end Formalism.IncomingBounds.FlowLoadBounds
