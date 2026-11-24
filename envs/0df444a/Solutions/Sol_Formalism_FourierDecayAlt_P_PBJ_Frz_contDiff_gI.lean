-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_gI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:25.322782+00:00
-- url     : https://prove2.me/submissions/9d797092-7607-4de0-9b38-4f1f76ea935f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_contDiff_zj
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_contDiff_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_contDiff_corner

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
theorem _root_.solution (β c : ℂ) {p : ℕ} {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p => gI β c Ψ q.1 q.2) := by
  unfold gI
  exact ((contDiff_psi β).comp (contDiff_corner p)).smul (hΨ.1.comp (contDiff_zj p _))
end Formalism.FourierDecayAlt.P.PBJ.Frz
