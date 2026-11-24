-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.contDiff_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:52:15.956962+00:00
-- url     : https://prove2.me/submissions/c8874f72-3674-4bc7-b628-06eb256c7a5c

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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {k r : ℕ} (M : B.Mat k r → Matrix n n ℂ)
    (hM : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun g => M g a b)) : ContDiff ℝ (⊤ : ℕ∞) (fun g => (M g).det) := by
  have hdet : (fun g => (M g).det) = fun g => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i := by
    funext g
    exact Matrix.det_apply' (M g)
  rw [hdet]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
end Formalism.FourierDecayAlt.P.JCx1
