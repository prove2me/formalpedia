-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.det_zj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:12.336872+00:00
-- url     : https://prove2.me/submissions/8a7252c0-ff11-473d-9b3e-464152daa7db

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block2_det_lower_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block2_det_upper_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block2_det_upper_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block2_det_lower_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block2_det_upper_triangular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
theorem _root_.solution {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin s) (Fin s) ℂ) : (Zj a b H C).det = H.det * C.det := by
  unfold Zj
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.FourierDecayAlt.P.Ux3.block2_det_lower_triangular, Formalism.FourierDecayAlt.P.Ux3.block2_det_lower_triangular,
    Formalism.FourierDecayAlt.P.Ux3.block2_det_upper_triangular]
  simp
end Formalism.FourierDecayAlt.P.PBJ.Frz
