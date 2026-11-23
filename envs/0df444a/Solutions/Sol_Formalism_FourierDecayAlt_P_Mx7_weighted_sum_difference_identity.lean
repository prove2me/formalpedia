-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.weighted_sum_difference_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:08.574853+00:00
-- url     : https://prove2.me/submissions/6fabb2aa-7659-4953-be09-65254b5a1325

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absLS

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
theorem _root_.solution (G b N S X Xp E : R) (hNS : N * S = S * N - b * S) (hbS : b * S = S * b)
    (hXS : X * S = S * Xp) (hSG : S * G = G * S) (hEN : Commute E N) (hEb : Commute E b) (c : ℂ) :
    G * X * (-N - c • b) * (S * E) = S * G * (Xp * E * ((-N - c • b) + b)) := by
  have hE : ((-N - c • b) + b) * E = E * ((-N - c • b) + b) :=
    (((hEN.neg_right).sub_right (hEb.smul_right c)).add_right hEb).eq.symm
  calc G * X * (-N - c • b) * (S * E) = G * X * ((-N - c • b) * S) * E := by simp only [mul_assoc]
    _ = G * (X * S) * (((-N - c • b) + b) * E) := by rw [absLS b N S hNS hbS]; simp only [mul_assoc]
    _ = G * (S * Xp) * (E * ((-N - c • b) + b)) := by rw [hXS, hE]
    _ = (G * S) * (Xp * E * ((-N - c • b) + b)) := by simp only [mul_assoc]
    _ = _ := by rw [← hSG]
end Formalism.FourierDecayAlt.P.Mx7
