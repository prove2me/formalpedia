-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absLG3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:51.16506+00:00
-- url     : https://prove2.me/submissions/5ae2284c-3e6b-4c51-986e-4ba6d18434f0

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
theorem _root_.solution (G b z N : R) (hNG : N * G = G * N - z) (hbG : b * G = G * b) (hGb : G * b = z) (c c' : ℂ)
    (hc : c = c' + 1) : (-N - c • b) * G = G * (-N - c' • b) := by
  have hNG' : N * G = G * N + -z := by rw [hNG, sub_eq_add_neg]
  rw [absLG G b (-z) N hNG' hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]
  abel
end Formalism.FourierDecayAlt.P.Mx7
