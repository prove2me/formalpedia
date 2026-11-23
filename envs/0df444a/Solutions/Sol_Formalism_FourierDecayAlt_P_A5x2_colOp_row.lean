-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.colOp_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:54.289688+00:00
-- url     : https://prove2.me/submissions/1979a3b3-df03-466e-8179-d5942b98f50a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_inv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det)
    (hξ : (Z⁻¹ *ᵥ m) c = 0) (a b : Fin n) :
    (Z + vecMulVec m (Pi.single c 1))⁻¹ a b = Z⁻¹ a b - (Z⁻¹ *ᵥ m) a * Z⁻¹ c b := by
  rw [← colOp_mul Z m c hZ, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (colOp_inv _ c hξ),
    Matrix.sub_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, vecMulVec_apply, Pi.single_apply]
end Formalism.FourierDecayAlt.P.A5x2
