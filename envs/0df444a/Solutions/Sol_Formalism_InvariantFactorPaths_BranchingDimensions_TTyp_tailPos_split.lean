-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.tailPos_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:49.179977+00:00
-- url     : https://prove2.me/submissions/bb25f016-6247-454a-a782-71ef1f8df42e

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf

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
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (n : ℕ) (la : ℕ → ℤ) {u : ℕ} (hu : u < n) :
    tailPos n la u = max (la u) 0 + tailPos n la (u + 1) := by
  unfold tailPos
  have hs : (range n).filter (fun m => u ≤ m) = insert u ((range n).filter (fun m => u + 1 ≤ m)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · intro h
      omega
    · intro h
      omega
  rw [hs, Finset.sum_insert (by simp)]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
