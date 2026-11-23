-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.in_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:56.4308+00:00
-- url     : https://prove2.me/submissions/a45137b1-95e7-447c-9f68-26ee8f626c84

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd

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
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowDualityReindexing
theorem _root_.solution (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)
end Formalism.IncomingBounds.FlowDualityReindexing
