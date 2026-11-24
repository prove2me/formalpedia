-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:13.965052+00:00
-- url     : https://prove2.me/submissions/e436fb78-b9d3-4188-b90c-ca5ae52b1494

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize

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
theorem _root_.solution (β : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => G.psi β w) := by
  unfold G.psi
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (((β * w).re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_const.mul contDiff_id))
  exact Complex.contDiff_exp.comp (contDiff_const.mul h1)
end Formalism.FourierDecayAlt.P.PBJ.Frz
