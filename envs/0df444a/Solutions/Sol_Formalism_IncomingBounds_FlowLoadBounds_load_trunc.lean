-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.load_trunc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:16.376875+00:00
-- url     : https://prove2.me/submissions/cfbdca39-70f1-4f3b-b698-8d9024373f9b

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
theorem _root_.solution (x : ZMod d → ℕ → ℝ) (s : ZMod d) :
    dpLoad l d (trunc d x) s = dpLoad l d x s := by
  simp only [dpLoad, trunc]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_ <;> simp [hi]
end Formalism.IncomingBounds.FlowLoadBounds
