-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Top.weylGT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:09.667618+00:00
-- url     : https://prove2.me/submissions/bc40e988-a8f0-40b5-bd75-3883e2554895

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_FinalT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_branchingDimensionFormula
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_weyl_dim_eq_gelfand_tsetlin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions Formalism.InvariantFactorPaths.BranchingDimensions.Top
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Top
theorem _root_.solution : ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ) :=
  weyl_dim_eq_gelfand_tsetlin branchingDimensionFormula
end Formalism.InvariantFactorPaths.BranchingDimensions.Top
