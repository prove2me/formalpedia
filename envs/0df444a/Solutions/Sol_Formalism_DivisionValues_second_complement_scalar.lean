-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:35:04.3056+00:00
-- url     : https://prove2.me/submissions/70efa2ca-5e2a-48a2-884a-33f66ab87741

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : Complement2Scalar := by
  intro K _ _ _ v0 hv0 cg hcg w
  have hcg0 : cg ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hcg
    exact zero_ne_one hcg
  have h1 : cg * star cg = 1 := by
    apply v0.embedding.injective
    rw [map_mul, hv0, map_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hcg]
    simp
  have h2 := ValuationRepresentative.vw_mul w cg (star cg) hcg0 (by rwa [ne_eq, star_eq_zero])
  rw [h1, ValuationRepresentative.vw_one, ValuationRepresentative.vw_star] at h2
  omega
end Formalism.DivisionValues
