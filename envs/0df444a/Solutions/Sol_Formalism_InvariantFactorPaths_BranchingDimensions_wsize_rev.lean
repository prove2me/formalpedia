-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.wsize_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:14.906783+00:00
-- url     : https://prove2.me/submissions/4eae7f6f-8803-4bc3-a902-8c1a81aa6607

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
theorem _root_.solution (n : ℕ) (la : ℕ → ℤ) : wsize n (revW n la) = - wsize n la := by
  unfold wsize revW
  rw [Finset.sum_neg_distrib]
  have h := Finset.sum_range_reflect (fun m => la m) n
  try simp only at h
  rw [h]
end Formalism.InvariantFactorPaths.BranchingDimensions
