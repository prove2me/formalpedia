-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Interl.size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:43.38881+00:00
-- url     : https://prove2.me/submissions/e70b2090-4b41-4178-b8a6-398ba9e1d965

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
namespace Interl
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) :
    b n ≤ wsize (n + 1) b - wsize n a ∧ wsize (n + 1) b - wsize n a ≤ b 0 := by
  constructor
  · unfold wsize
    rw [Finset.sum_range_succ]
    have h1 : ∑ m ∈ range n, a m ≤ ∑ m ∈ range n, b m :=
      Finset.sum_le_sum fun m hm => (h m (Finset.mem_range.mp hm)).1
    linarith
  · unfold wsize
    rw [Finset.sum_range_succ']
    have h1 : ∑ m ∈ range n, b (m + 1) ≤ ∑ m ∈ range n, a m :=
      Finset.sum_le_sum fun m hm => (h m (Finset.mem_range.mp hm)).2
    linarith
end Interl
end Formalism.InvariantFactorPaths.BranchingDimensions
