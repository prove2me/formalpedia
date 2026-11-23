-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.commutator_expansion_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:51.895885+00:00
-- url     : https://prove2.me/submissions/c435bfe6-a256-408a-9bfa-a0ae474f8fad

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
theorem _root_.solution (a ap am S Ss Nn Nd : R) (h1 : Ss * a = ap * Ss) (h2 : S * a = am * S) (hn : Ss * S = Nn)
    (hd : S * Ss = Nd) : a * Ss * (a * S) - a * S * (a * Ss) = a * ap * Nn - a * am * Nd := by
  have e1 : a * Ss * (a * S) = a * ap * (Ss * S) := by
    calc a * Ss * (a * S) = a * (Ss * a) * S := by simp only [mul_assoc]
      _ = _ := by rw [h1]; simp only [mul_assoc]
  have e2 : a * S * (a * Ss) = a * am * (S * Ss) := by
    calc a * S * (a * Ss) = a * (S * a) * Ss := by simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [mul_assoc]
  rw [e1, e2, hn, hd]
end Formalism.FourierDecayAlt.P.Mx7
