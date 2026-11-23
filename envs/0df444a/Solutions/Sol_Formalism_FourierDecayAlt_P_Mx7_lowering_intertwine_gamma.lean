-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.lowering_intertwine_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:58.272465+00:00
-- url     : https://prove2.me/submissions/567f7477-9486-4855-8218-6107f31a87b0

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
theorem _root_.solution (G Gi X L0 L1 U U' : R) (hLG : L0 * G = G * L1) (hXL : Commute X L1) (hUX : U * X = X * U')
    (hGU : Commute G U) (hGiX : Commute Gi X) (hGGi : Commute G Gi) :
    (L0 + Gi * U) * (G * X) = (G * X) * (L1 + Gi * U') := by
  have a : L0 * (G * X) = G * X * L1 := by rw [← mul_assoc, hLG, mul_assoc, mul_assoc, hXL.eq]
  have b : Gi * U * (G * X) = G * X * (Gi * U') := by
    calc Gi * U * (G * X) = Gi * (U * G) * X := by simp only [mul_assoc]
      _ = Gi * (G * U) * X := by rw [hGU.eq]
      _ = (Gi * G) * (U * X) := by simp only [mul_assoc]
      _ = (G * Gi) * (X * U') := by rw [hUX, hGGi.eq]
      _ = G * (Gi * X) * U' := by simp only [mul_assoc]
      _ = G * (X * Gi) * U' := by rw [hGiX.eq]
      _ = _ := by simp only [mul_assoc]
  rw [add_mul, mul_add, a, b]
end Formalism.FourierDecayAlt.P.Mx7
