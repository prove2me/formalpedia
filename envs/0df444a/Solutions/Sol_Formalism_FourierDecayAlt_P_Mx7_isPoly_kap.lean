-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isPoly_kap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:01:57.415485+00:00
-- url     : https://prove2.me/submissions/7b5b86ae-c35c-481d-829b-d71a1bfa1216

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (p : Ty P → ℂ[X]) : IsPoly (fun Y => kap P fun π => (p π).eval Y) := by
  have h : ∀ Y, (kap P fun π => (p π).eval Y) =
      ∑ π : Ty P, algebraMap ℂ (A P) ((p π).eval Y) * kap P (fun j => if π = j then 1 else 0) := by
    intro Y
    conv_lhs => rw [pi_eq_sum_univ (fun π => (p π).eval Y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [map_smul, Algebra.smul_def]
  exact (IsPoly.sum _ _ fun π _ => (IsPoly.scalar (p π)).mul (IsPoly.const _)).congr h
end Formalism.FourierDecayAlt.P.Mx7
