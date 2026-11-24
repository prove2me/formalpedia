-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.WGT.wsize_extW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.799805+00:00
-- url     : https://prove2.me/submissions/99ba206f-e9e0-4370-bb78-7e14952e6e8d

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_extW_val

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
open Formalism.InvariantFactorPaths.BranchingDimensions.WGT
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)
namespace Formalism.InvariantFactorPaths.BranchingDimensions.WGT
theorem _root_.solution {n : ℕ} (μ : Fin n → ℤ) : wsize n (extW μ) = ∑ m, μ m := by
  rw [wsize, Finset.sum_range]
  simp [extW_val]
end Formalism.InvariantFactorPaths.BranchingDimensions.WGT
