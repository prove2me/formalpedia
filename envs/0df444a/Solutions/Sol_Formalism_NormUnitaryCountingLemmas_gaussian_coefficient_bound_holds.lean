-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.gaussian_coefficient_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:41.385001+00:00
-- url     : https://prove2.me/submissions/c0af826c-9fce-4ba3-9c0f-313913e0badb

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_GaussianCoefficientFactorialBound
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_norm_sq_coeff_le_gaussian_growth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open ExponentialIntegralMeasures
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution : N1 := by
  intro G Θ c S hΘ hS e
  have h := norm_sq_coeff_le_gaussian_growth G Θ c S hΘ hS e
  have hpos : 0 < ∏ i, ((e i : ℝ)) ^ e i := by
    apply Finset.prod_pos
    intro i _
    rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0]; simp
    · positivity
  have hprod : ∏ i, (Real.exp 1 / (e i : ℝ)) ^ e i =
      Real.exp (∑ i, (e i : ℝ)) / ∏ i, ((e i : ℝ)) ^ e i := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.exp_nat_mul, mul_one]
  rw [hprod, ← mul_div_assoc, le_div_iff₀ hpos]
  exact h
end Formalism.NormUnitaryCountingLemmas
