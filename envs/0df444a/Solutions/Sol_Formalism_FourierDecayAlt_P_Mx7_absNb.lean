-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absNb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:51.145867+00:00
-- url     : https://prove2.me/submissions/2044c2f9-8375-4516-b5d5-0355a1b41eeb

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
theorem _root_.solution (zb Gi N : R) (hNzb : N * zb = zb * N) (hNGi : N * Gi = Gi * N - zb * Gi * Gi)
    (hc : Gi * zb = zb * Gi) : N * (zb * Gi) = (zb * Gi) * N - (zb * Gi) * (zb * Gi) := by
  rw [← mul_assoc, hNzb, mul_assoc, hNGi, mul_sub, ← mul_assoc zb Gi N, mul_assoc zb Gi (zb * Gi),
    ← mul_assoc Gi zb Gi, hc]
end Formalism.FourierDecayAlt.P.Mx7
