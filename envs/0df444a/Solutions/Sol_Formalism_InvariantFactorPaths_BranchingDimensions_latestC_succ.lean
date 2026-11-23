-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.latestC_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:30.972089+00:00
-- url     : https://prove2.me/submissions/0b922f1a-cfc5-4164-92c4-cdf8ea9a8108

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latest_succ

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
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (i : ℕ) (hi : i + 1 ≤ D.n0) :
    D.latestC (i + 1) = if (!D.vec (i + 1)) = true then D.B (i + 1) :: D.latestC i else D.latestC i := by
  unfold Letters.latestC
  rw [min_eq_left hi, min_eq_left (by omega)]
  exact latest_succ (fun l => !D.vec l) D.B i
end Formalism.InvariantFactorPaths.BranchingDimensions
