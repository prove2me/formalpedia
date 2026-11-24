-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pathEntryBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:47.9411+00:00
-- url     : https://prove2.me/submissions/3409de14-fd2d-4ccd-a7b7-59fde0394e8f

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pre_of_path
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pre_size
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_path_rows

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
theorem _root_.solution : PathEntryBounds := by
  intro D mu hW hP
  have hk : 1 ≤ D.k := by
    have := hW.1
    unfold Letters.k
    omega
  exact ⟨pre_size hk (pre_of_path hP), path_rows hP⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
