-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.primitive_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:31:17.409293+00:00
-- url     : https://prove2.me/submissions/2a7b004f-4b68-492f-bcea-792c2eb8f42d

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : PrimitiveLine := by
  intro R K σ _ _ _ hinj Del Q m c hD hc
  have hcoef : c = algebraMap R K (Q.coeff m) := by
    have h1 := congrArg (MvPolynomial.coeff m) hc
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, hD, map_one, smul_eq_mul,
      mul_one] at h1
    exact h1
  refine ⟨Q.coeff m, hcoef.symm, ?_⟩
  have hmap : MvPolynomial.map (algebraMap R K) Q = MvPolynomial.map (algebraMap R K) (Q.coeff m • Del) := by
    rw [← hc, hcoef, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  first
    | exact MvPolynomial.map_injective _ hinj hmap
    | exact MvPolynomial.map_injective hinj hmap
end Formalism.EigenvalueLevelCeiling
