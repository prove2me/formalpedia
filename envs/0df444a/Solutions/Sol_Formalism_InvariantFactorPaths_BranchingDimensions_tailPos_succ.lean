-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.tailPos_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:48.084931+00:00
-- url     : https://prove2.me/submissions/58a3c3e3-2976-463a-86c5-1dd3c27d57fd

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
theorem _root_.solution (n : ℕ) (la : ℕ → ℤ) (u : ℕ) :
    tailPos (n + 1) la u = tailPos n la u + if u ≤ n then max (la n) 0 else 0 := by
  unfold tailPos
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ]
end Formalism.InvariantFactorPaths.BranchingDimensions
