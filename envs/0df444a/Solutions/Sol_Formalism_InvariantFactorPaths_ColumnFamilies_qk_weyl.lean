-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_weyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:51.139742+00:00
-- url     : https://prove2.me/submissions/c7750ad7-5a73-43c5-b663-0f906d7fae16

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_prod_conv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_W_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_extW_val
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (mu : Fin n → ℤ) :
    Formalism.InvariantFactorPaths.BranchingDimensions.weylDim n (Formalism.InvariantFactorPaths.BranchingDimensions.extW mu) * vandermondeDenominator n = qk_D (qk_v mu) := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.weylDim
  simp_rw [prod_div_distrib]
  rw [show (∏ j ∈ range n, ∏ i ∈ range j, ((j : ℝ) - (i : ℝ))) = vandermondeDenominator n from rfl, div_mul_cancel₀ _ (qk_W_ne n),
    qk_prod_conv n (fun i j => ((Formalism.InvariantFactorPaths.BranchingDimensions.extW mu i - Formalism.InvariantFactorPaths.BranchingDimensions.extW mu j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ)))]
  unfold qk_D qk_v
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  rw [Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val, Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_val]
  push_cast
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
