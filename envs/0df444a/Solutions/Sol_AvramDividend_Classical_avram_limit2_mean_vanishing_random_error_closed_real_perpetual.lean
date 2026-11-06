-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_mean_vanishing_random_error_closed_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:51:00.531524+00:00
-- url     : https://prove2.me/submissions/66783f09-1cf1-4af3-b547-8c04df3ae5c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_vanishing_remainder_closed_cash_real_perpetual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Mean-vanishing random nonnegative source errors permit original closed
    perpetual value and exact signed real payout bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → Ω → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫⁻ ω, error n ω ∂P) ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
      B + (∫⁻ ω, error n ω ∂P)) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  exact avram_limit2_vanishing_remainder_closed_cash_real_perpetual
    X q x D hD B hB (fun n => ∫⁻ ω, error n ω ∂P) hError hBudget
