-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.contDiff_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:52:19.058802+00:00
-- url     : https://prove2.me/submissions/347c2a48-fe8f-4eec-8974-66854d84abb6

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces

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
theorem _root_.solution : ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => Complex.normSq c) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => c.re) := Complex.reCLM.contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => c.im) := Complex.imCLM.contDiff
  have e : (fun c : ℂ => Complex.normSq c) = fun c => c.re * c.re + c.im * c.im :=
    funext Complex.normSq_apply
  rw [e]
  exact (h1.mul h1).add (h2.mul h2)
end Formalism.FourierDecayAlt.P.JCx1
