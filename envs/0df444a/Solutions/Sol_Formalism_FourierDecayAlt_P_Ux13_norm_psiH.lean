-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.norm_psiH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:30:58.34468+00:00
-- url     : https://prove2.me/submissions/0f4c24d4-cb30-443a-859f-675ce13802c4

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
namespace Formalism.FourierDecayAlt.P.Ux13
theorem _root_.solution {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) (η : XiH p s σ) : ‖psiH β σ η‖ = 1 := by
  simp only [psiH, G.psi]
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
end Formalism.FourierDecayAlt.P.Ux13
