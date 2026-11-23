-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.commutator_four_commuting
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:51.933621+00:00
-- url     : https://prove2.me/submissions/20c3acdd-ebac-470b-bf34-dafd1bd5192b

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
theorem _root_.solution (a b S Ss : R) (h1 : Ss * b = b * Ss) (h2 : S * a = a * S) (hab : a * b = b * a)
    (hm : Ss * S = S * Ss) : a * Ss * (b * S) - b * S * (a * Ss) = 0 := by
  have e1 : a * Ss * (b * S) = a * b * (Ss * S) := by
    calc a * Ss * (b * S) = a * (Ss * b) * S := by simp only [mul_assoc]
      _ = _ := by rw [h1]; simp only [mul_assoc]
  have e2 : b * S * (a * Ss) = b * a * (S * Ss) := by
    calc b * S * (a * Ss) = b * (S * a) * Ss := by simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [mul_assoc]
  rw [e1, e2, hab, hm, sub_self]
end Formalism.FourierDecayAlt.P.Mx7
