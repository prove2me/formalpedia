-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:51.801803+00:00
-- url     : https://prove2.me/submissions/c982b240-e1a3-4da0-8fb8-19920065aea8

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
theorem _root_.solution (G b zb N : R) (hGb : G * b = zb) (hNb : N * b = b * N - b * b) (cu cv : ℂ) :
    (G * (-N - cu • b) - zb) * (-N - cv • b) =
      G * N * N + (cu + cv + 1) • (zb * N) + (cu * cv) • (zb * b) := by
  have h1 : G * (-N - cu • b) - zb = -(G * N) - (cu + 1) • zb := by
    rw [mul_sub, mul_neg, mul_smul_comm, hGb]; module
  have h2 : G * N * b = zb * N - zb * b := by
    rw [mul_assoc, hNb, mul_sub, ← mul_assoc, ← mul_assoc, hGb]
  rw [h1]
  simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, h2]
  module
end Formalism.FourierDecayAlt.P.Mx7
