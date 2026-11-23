-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absUX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:25.725204+00:00
-- url     : https://prove2.me/submissions/2ec28c56-bfd0-428d-ba40-1ae3952e8cbd

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
theorem _root_.solution (a g S X a' e : R) (s1 : g * S = S * X) (s2 : a * g = e) (s3 : X * a' = e) :
    a * S * X = X * (a' * S) := by
  calc a * S * X = a * (S * X) := mul_assoc _ _ _
    _ = a * (g * S) := by rw [s1]
    _ = (a * g) * S := (mul_assoc _ _ _).symm
    _ = (X * a') * S := by rw [s2, s3]
    _ = _ := mul_assoc _ _ _
end Formalism.FourierDecayAlt.P.Mx7
