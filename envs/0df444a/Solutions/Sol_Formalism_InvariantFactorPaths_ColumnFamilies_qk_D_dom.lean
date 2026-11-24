-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:09.039639+00:00
-- url     : https://prove2.me/submissions/4f61012d-de88-4146-a43a-7cf562082916

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_weyl
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
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {mu : Fin n → ℤ} (h : Dominant mu) : qk_D (qk_v mu) = (dGT n mu : ℝ) * vandermondeDenominator n := by
  rw [← qk_weyl, Formalism.InvariantFactorPaths.BranchingDimensions.weyl_dim_eq_gelfand_tsetlin Formalism.InvariantFactorPaths.BranchingDimensions.branchingDimensionFormula n mu h]
end Formalism.InvariantFactorPaths.ColumnFamilies
