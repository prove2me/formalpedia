-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.zj_apply_ll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:38.181825+00:00
-- url     : https://prove2.me/submissions/ca1bb9da-de83-4c70-b1cf-ab6279d3b73d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_z_affine


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
theorem _root_.solution {p : ℕ} (a : Fin 1 → Fin p → ℂ) (b : Fin p → Fin 1 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin 1) (Fin 1) ℂ) (i j : Fin p) : Zj a b H C (Fin.castAdd 1 i) (Fin.castAdd 1 j) = H i j := by
  rw [Formalism.FourierDecayAlt.P.level_z_affine]
  simp [blk2]
end Formalism.FourierDecayAlt.P.PBJ.Frz
