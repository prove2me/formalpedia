-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:43.551819+00:00
-- url     : https://prove2.me/submissions/fd7548be-75a8-4370-a1fb-293dda2af928

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absLG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
variable {R : Type*} [Ring R] [Algebra ℂ R]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (G b zb N X X' : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b)
    (hG : Commute X' G) (hb : Commute X' b) (hN : Commute X' N) (hzb : Commute X' zb) (cu cv : ℂ) :
    (G * X * (-N - cu • b)) * (G * X' * (-N - cv • b)) =
      G * (X * X') * ((G * (-N - cu • b) - zb) * (-N - cv • b)) := by
  have hc : (G * (-N - cu • b) - zb) * X' = X' * (G * (-N - cu • b) - zb) :=
    ((hG.mul_right ((hN.neg_right).sub_right (hb.smul_right cu))).sub_right hzb).eq.symm
  calc (G * X * (-N - cu • b)) * (G * X' * (-N - cv • b))
      = G * X * ((-N - cu • b) * G) * X' * (-N - cv • b) := by simp only [mul_assoc]
    _ = G * X * ((G * (-N - cu • b) - zb) * X') * (-N - cv • b) := by
        rw [absLG G b zb N hNG hbG]; simp only [mul_assoc]
    _ = _ := by rw [hc]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Mx7
