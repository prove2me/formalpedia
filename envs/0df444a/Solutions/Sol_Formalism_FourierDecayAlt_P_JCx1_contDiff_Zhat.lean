-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.contDiff_Zhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:21.414052+00:00
-- url     : https://prove2.me/submissions/2eef4fe6-1b01-4503-b924-891b00f178ca

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.JCx1
theorem _root_.solution {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Zhat k r z z' g a b) := by
  unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
  simp only [dotProduct, Matrix.mulVec]
  exact ContDiff.sum fun i _ => contDiff_const.mul (ContDiff.sum fun j _ => contDiff_const.mul
    (ContDiff.sum fun l _ => (contDiff_entry j l).mul contDiff_const))
end Formalism.FourierDecayAlt.P.JCx1
