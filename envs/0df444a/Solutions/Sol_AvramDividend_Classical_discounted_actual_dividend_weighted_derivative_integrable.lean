-- Prove2me | solution 1 for AvramDividend.Classical.discounted_actual_dividend_weighted_derivative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:20:14.443975+00:00
-- url     : https://prove2.me/submissions/25fcd3af-3cf5-48fb-a534-d0522d4f880d

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A finite-valued dividend strategy has finite Stieltjes mass in every stopped payment window. If the discounted derivative-weighted payout is measurable and the derivative is bounded there, the weighted integral is absolutely integrable. The proof controls the exponential discount by one and applies finite-measure bounded-integrand integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (w u : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) * deriv w (u t))
      (dividendMeasure D ω))
    (hbound : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ),
      |deriv w (u t)| ≤ M) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q * t)) * deriv w (u t))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by
  refine Measure.integrableOn_of_bounded (M := M)
    (dividendMeasure_paymentWindow_finite_of_strategy D hD ω σ T)
    hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    ((paymentTimes_measurable σ).inter measurableSet_Iic)] with t ht
  have hqt : 0 ≤ q * t := mul_nonneg hq ht.1.1
  have hExp : Real.exp (-(q * t)) ≤ 1 := by
    calc
      Real.exp (-(q * t)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr hqt)
      _ = 1 := Real.exp_zero
  calc
    ‖Real.exp (-(q * t)) * deriv w (u t)‖ =
        Real.exp (-(q * t)) * |deriv w (u t)| := by
          simp only [Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(q * t)) * M :=
        mul_le_mul_of_nonneg_left (hbound t ht)
          (le_of_lt (Real.exp_pos _))
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hExp hM
    _ = M := one_mul M
