-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.flowVal_trunc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:58.055801+00:00
-- url     : https://prove2.me/submissions/b7b01c6b-59b6-4075-abe3-413402ef6193

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
theorem _root_.solution (x : ZMod d → ℕ → ℝ) : flowVal d (trunc d x) = flowVal d x := by
  simp only [Formalism.IncomingBounds.flowVal, trunc]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i hi => if_pos hi
end Formalism.IncomingBounds.FlowLoadBounds
