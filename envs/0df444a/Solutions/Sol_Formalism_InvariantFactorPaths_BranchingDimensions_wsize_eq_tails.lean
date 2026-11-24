-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.wsize_eq_tails
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:14.974677+00:00
-- url     : https://prove2.me/submissions/b2ffb241-b531-4660-8bb2-1f1e28bef318

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (n : ℕ) (a : ℕ → ℤ) : wsize n a = tailPos n a 0 - tailPos n (revW n a) 0 := by
  unfold wsize tailPos revW
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [Nat.zero_le, if_true, ite_true]
  have h := Finset.sum_range_reflect (fun m => max (-(a m)) 0) n
  try simp only at h
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases le_total 0 (a m) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h0, max_eq_left (by linarith)]
    ring
end Formalism.InvariantFactorPaths.BranchingDimensions
