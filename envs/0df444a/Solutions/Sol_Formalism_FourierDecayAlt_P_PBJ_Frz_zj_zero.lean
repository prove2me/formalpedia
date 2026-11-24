-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.zj_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:11.86068+00:00
-- url     : https://prove2.me/submissions/021ba846-577e-4778-8e4d-8d213525c9b3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_block_two_one_lower_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_block_two_one_upper_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_block_two_diagonal_zero_size

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
theorem _root_.solution {p : ℕ} (a : Fin 0 → Fin p → ℂ) (b : Fin p → Fin 0 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z : Matrix (Fin 0) (Fin 0) ℂ) : (Zj a b H Z : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = H := by
  unfold Zj
  rw [block_two_one_lower_zero, block_two_one_upper_zero, block_two_diagonal_zero_size, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.PBJ.Frz
