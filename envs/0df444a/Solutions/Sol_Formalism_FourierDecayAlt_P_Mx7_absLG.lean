-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absLG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:18.669802+00:00
-- url     : https://prove2.me/submissions/8bd3dcf3-4b14-4b57-af1b-f1f569a52994

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

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
theorem _root_.solution (G b zb N : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b) (c : ℂ) :
    (-N - c • b) * G = G * (-N - c • b) - zb := by
  rw [sub_mul, neg_mul, smul_mul_assoc, hNG, hbG, mul_sub, mul_neg, mul_smul_comm]; abel
end Formalism.FourierDecayAlt.P.Mx7
