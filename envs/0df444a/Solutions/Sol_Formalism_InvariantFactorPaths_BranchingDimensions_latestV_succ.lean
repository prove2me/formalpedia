-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.latestV_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:31.256814+00:00
-- url     : https://prove2.me/submissions/747d9e16-ecd9-404c-8c01-0660cfaaabd4

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
    D.latestV (i + 1) = if D.vec (i + 1) = true then D.B (i + 1) :: D.latestV i else D.latestV i := by
  unfold Letters.latestV
  rw [min_eq_left hi, min_eq_left (by omega)]
  exact latest_succ D.vec D.B i
end Formalism.InvariantFactorPaths.BranchingDimensions
