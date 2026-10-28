-- Prove2me | solution 1 for AvramDividend.Classical.expected_discounted_actual_dividend_le_derivative_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:27:32.74288+00:00
-- url     : https://prove2.me/submissions/b7e8df16-9555-4173-97e7-a41680aa80c3

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_actual_dividend_le_derivative_weighted
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_real_lintegral_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The expected actual stopped dividend payout is no greater than the
    derivative-weighted Stieltjes integral after the real/extended-real bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞) (T : ℝ≥0)
    (w : ℝ → ℝ) (u : Ω → ℝ → ℝ)
    (hgrad : ∀ ω t, t ∈ paymentTimes (σ ω) ∩ Iic (T : ℝ) →
      1 ≤ deriv w (u ω t))
    (hWeighted : ∀ ω, IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u ω t))
      (paymentTimes (σ ω) ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal
      (∫ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) * deriv w (u ω t)
          ∂(dividendMeasure D ω)) ∂P) := by
  apply lintegral_mono
  intro ω
  have hbridge :=
    discounted_dividend_window_real_lintegral_bridge
      D hD q hq (σ ω) T ω
  have hpath :=
    discounted_actual_dividend_le_derivative_weighted
      D hD q hq (σ ω) T ω w (u ω)
      (fun t ht => hgrad ω t ht) (hWeighted ω)
  exact hbridge.le.trans (ENNReal.ofReal_le_ofReal hpath)
