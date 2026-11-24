-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.psiH_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:56:58.776425+00:00
-- url     : https://prove2.me/submissions/4d0fe60e-3c00-42bd-8623-0cd777d058de

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_psi_add


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
theorem _root_.solution (β : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (η : XiH p 1 σ) :
    psiH β σ η = G.psi β (subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) + supS (G.upper η.2.2)) *
      G.psi β (cornerA η.1.1 + cornerB η.1.2) := by
  unfold psiH
  rw [← Formalism.FourierDecayAlt.P.G8.psi_add]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.PBJ.Frz
