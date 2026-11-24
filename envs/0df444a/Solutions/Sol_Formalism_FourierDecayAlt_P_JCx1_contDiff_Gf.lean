-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:02.134847+00:00
-- url     : https://prove2.me/submissions/1fedb994-79c4-4313-8e65-24221bb67c26

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_Dmin
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_normSq

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
theorem _root_.solution {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => Formalism.QuantumDeterminants.Gf k r z z' g) := by
  unfold Formalism.QuantumDeterminants.Gf
  exact (contDiff_normSq.comp (contDiff_Dmin z z' _)).sub
    (contDiff_const.mul (contDiff_normSq.comp (contDiff_Dmin z z' _)))
end Formalism.FourierDecayAlt.P.JCx1
