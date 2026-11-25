-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.logBinomialProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:20.843999+00:00
-- url     : https://prove2.me/submissions/d1c80d6c-fa32-49ac-8637-4ee9d624dc8f

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_nat
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_hasDerivAt
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__anti_c3dd9c16a389
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower_0adb6efea0e8
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__upper_3321829bdfec
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__pos_68c1bbd5fc8b
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower2_d91edae1b020
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__half_e845f6006a1c
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_concave

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
theorem _root_.solution : LogBinomialProperties := by
  intro k'
  exact ⟨fT_zero k', fT_nat k', fT_hasDerivAt k', fT'_pos k', fT'_anti k',
    fun y hy _ => ⟨fT'_lower k' y hy, fT'_upper k' y hy⟩, fT'_lower2 k', fT'_half k', fT_concave k'⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
