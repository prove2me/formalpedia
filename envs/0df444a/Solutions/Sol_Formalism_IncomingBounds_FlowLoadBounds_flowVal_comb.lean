-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.flowVal_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:08.298774+00:00
-- url     : https://prove2.me/submissions/e079c60a-5d07-47b3-b530-c2fabd119623

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842

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
theorem _root_.solution (x y : ZMod d → ℕ → ℝ) (a b : ℝ) :
    flowVal d (fun s i => a * x s i + b * y s i) = a * flowVal d x + b * flowVal d y := by
  calc Formalism.IncomingBounds.flowVal d (fun s i => a * x s i + b * y s i)
        = ∑ s, (a * ∑ i ∈ oddLevels d, x s i + b * ∑ i ∈ oddLevels d, y s i) :=
          Finset.sum_congr rfl fun s _ => sum_comb' _ _ _ _ _
    _ = a * Formalism.IncomingBounds.flowVal d x + b * Formalism.IncomingBounds.flowVal d y := sum_comb' _ _ _ _ _
end Formalism.IncomingBounds.FlowLoadBounds
