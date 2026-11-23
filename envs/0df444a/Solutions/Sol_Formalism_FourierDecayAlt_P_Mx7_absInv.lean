-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:50.308781+00:00
-- url     : https://prove2.me/submissions/d0440c31-bf43-4b5b-b90e-8149c75ffb15

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
theorem _root_.solution (G Gi X Xi : R) (hG : G * Gi = 1) (hG' : Gi * G = 1) (hX : X * Xi = 1) (hX' : Xi * X = 1)
    (c : Commute X Gi) (c' : Commute Xi G) : (G * X) * (Gi * Xi) = 1 ∧ (Gi * Xi) * (G * X) = 1 := by
  constructor
  · calc (G * X) * (Gi * Xi) = G * (X * Gi) * Xi := by simp only [mul_assoc]
      _ = (G * Gi) * (X * Xi) := by rw [c.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hG, hX, one_mul]
  · calc (Gi * Xi) * (G * X) = Gi * (Xi * G) * X := by simp only [mul_assoc]
      _ = (Gi * G) * (Xi * X) := by rw [c'.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hG', hX', one_mul]
end Formalism.FourierDecayAlt.P.Mx7
