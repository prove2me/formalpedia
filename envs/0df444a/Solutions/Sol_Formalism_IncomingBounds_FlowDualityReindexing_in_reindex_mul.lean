-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.in_reindex_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:06.821424+00:00
-- url     : https://prove2.me/submissions/257cd4af-9eda-40a9-a5b0-baba699ca8e0

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
theorem _root_.solution (sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, sig s * ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i * sig (s + (i : ZMod d)) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => ?_)
  rw [Equiv.subRight_apply, sub_add_cancel, mul_comm]
end Formalism.IncomingBounds.FlowDualityReindexing
