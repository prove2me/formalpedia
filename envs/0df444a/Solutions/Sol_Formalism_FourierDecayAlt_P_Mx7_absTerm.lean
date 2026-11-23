-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:25.548093+00:00
-- url     : https://prove2.me/submissions/a9ccd063-0b4c-410d-a73e-98558dab0c27

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
theorem _root_.solution (X k Gi S : R) (h1 : Commute X k) (h2 : Commute X (Gi * S)) (c : Commute Gi k) :
    Commute X (Gi * (k * S)) := by
  have : Gi * (k * S) = k * (Gi * S) := by rw [← mul_assoc, c.eq, mul_assoc]
  rw [this]; exact h1.mul_right h2
end Formalism.FourierDecayAlt.P.Mx7
