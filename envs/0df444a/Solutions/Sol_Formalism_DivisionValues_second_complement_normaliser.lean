-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_normaliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:24:29.493286+00:00
-- url     : https://prove2.me/submissions/456b233e-46c4-484a-b3f7-cdf17e4388ce

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_pow
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
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
theorem _root_.solution : Complement2Normaliser := by
  intro K _ _ _ g hg pb hpb Psi _ p ν hp w
  have hg0 : (g : K) ≠ 0 := natCast_ne_zero' hg
  have hpb0 : pb ≠ 0 := by
    intro h
    apply hg0
    rw [← hpb, h, zero_mul]
  have hprod : ∏ τ, p τ ^ ν τ = pb ^ (∑ τ, ν τ) := by
    simp only [hp]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, vw_pow w pb hpb0, vw_pow (conjPl w) pb hpb0, ← hpb,
    ValuationRepresentative.vw_mul w _ _ hpb0 (by rwa [ne_eq, star_eq_zero]), ValuationRepresentative.vw_star]
  ring
end Formalism.DivisionValues
