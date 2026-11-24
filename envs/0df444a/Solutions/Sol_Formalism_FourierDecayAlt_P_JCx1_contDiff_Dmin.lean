-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:06.715623+00:00
-- url     : https://prove2.me/submissions/36846d6e-c689-4673-a4cd-f187a2a6ee58

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_Zhat

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
theorem _root_.solution {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) := by
  unfold Formalism.QuantumDeterminants.Dmin
  exact contDiff_det _ fun a b => contDiff_Zhat z z' _ _
end Formalism.FourierDecayAlt.P.JCx1
