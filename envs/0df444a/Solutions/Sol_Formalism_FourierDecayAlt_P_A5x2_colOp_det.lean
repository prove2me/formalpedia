-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.colOp_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.977056+00:00
-- url     : https://prove2.me/submissions/d1cd1645-6d51-494b-807d-cf75ea7dd4db

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det)
    (hξ : (Z⁻¹ *ᵥ m) c = 0) : IsUnit (Z + vecMulVec m (Pi.single c 1)).det := by
  rw [← colOp_mul Z m c hZ, Matrix.det_mul]
  exact hZ.mul (Matrix.isUnit_det_of_right_inverse (colOp_inv _ c hξ))
end Formalism.FourierDecayAlt.P.A5x2
