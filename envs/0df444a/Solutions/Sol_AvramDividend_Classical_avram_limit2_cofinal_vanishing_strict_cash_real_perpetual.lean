-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_cofinal_vanishing_strict_cash_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:57:16.822985+00:00
-- url     : https://prove2.me/submissions/e7c34106-bc24-4b5e-9163-68eb0bed6a09

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_real_cofinal_family_is_tail_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_limit2_tail_cofinal_vanishing_strict_cash_real_perpetual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Ordinary real cofinality suffices for vanishing-error original strict
    cash bounds and exact signed perpetual Stieltjes expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hCofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  exact avram_limit2_tail_cofinal_vanishing_strict_cash_real_perpetual
    X q x D hD T
      (avram_limit2_real_cofinal_family_is_tail_cofinal T hCofinal)
      B hB error hError hBudget
