-- Prove2me | solution 1 for AvramDividend.Classical.discounted_actual_dividend_le_derivative_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:19:08.250987+00:00
-- url     : https://prove2.me/submissions/265a8649-f963-4307-a9b9-9b45e79ccc4d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_integrableOn_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For a finite-valued admissible dividend strategy and any stopped payment window, if the candidate's derivative along a measurable reserve profile is at least one and its derivative-weighted discounted payout is integrable, the actual discounted payout is no greater than the derivative-weighted payout. Integrability of the unweighted discount follows directly from finite strategy payment mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (w u : ℝ → ℝ)
    (hgrad : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ), 1 ≤ deriv w (u t))
    (hWeighted : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u t))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) * deriv w (u t) ∂(dividendMeasure D ω)) := by
  apply MeasureTheory.integral_mono_ae
    (discounted_dividend_window_integrableOn_of_strategy
      D hD q hq σ T ω) hWeighted
  filter_upwards [MeasureTheory.ae_restrict_mem
    ((paymentTimes_measurable σ).inter measurableSet_Iic)] with t ht
  have h := mul_le_mul_of_nonneg_left (hgrad t ht)
    (le_of_lt (Real.exp_pos (-(q * t))))
  simpa using h
