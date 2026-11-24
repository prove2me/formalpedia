-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.cs_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:57.257796+00:00
-- url     : https://prove2.me/submissions/5d8e65df-13b5-436b-b293-a4eb03500219

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_in_reindex_mul

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
theorem _root_.solution (D sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, D s * sig s - flowVal d x =
      ∑ s : ZMod d, sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
        (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) +
      ∑ s : ZMod d, ∑ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) := by
  have hA : ∑ s : ZMod d, sig s * (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i * ((l : ℝ) ^ i * sig s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, in_reindex_mul]
  simp only [mul_one]
  unfold Formalism.IncomingBounds.flowVal
  rw [show ∑ s : ZMod d, D s * sig s = ∑ s : ZMod d, sig s * D s from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _]
  ring
end Formalism.IncomingBounds.FlowDualityReindexing
