-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absCombo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:50.323213+00:00
-- url     : https://prove2.me/submissions/392a08a7-2d31-4c99-a39b-d10e776db407

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
theorem _root_.solution {C : Type*} [CommRing C] [Algebra ℂ C] (κ : C →ₐ[ℂ] R) (N b : R) (φ1 φ2 ψ1 ψ2 : C) (cu cv : ℂ)
    (h1 : φ1 + φ2 = ψ1 + ψ2) (h2 : (1 - cu) • φ1 - cv • φ2 = (1 - cv) • ψ1 - cu • ψ2) :
    κ φ1 * ((-N - cu • b) + b) + κ φ2 * (-N - cv • b) = κ ψ1 * ((-N - cv • b) + b) + κ ψ2 * (-N - cu • b) := by
  have e1 := congrArg (fun f => κ f * N) h1
  have e2 := congrArg (fun f => κ f * b) h2
  simp only [map_add, map_sub, map_smul, add_mul, sub_mul, smul_mul_assoc] at e1 e2
  simp only [mul_add, mul_sub, mul_neg, mul_smul_comm]
  linear_combination (norm := module) -e1 + e2
end Formalism.FourierDecayAlt.P.Mx7
