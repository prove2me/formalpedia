-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_positive_strict_cash_to_perpetual_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:01:27.17188+00:00
-- url     : https://prove2.me/submissions/1cb04bc2-5236-40f6-8549-6cde481b504b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞)
    (hStrict : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by
  have hClosed :
      ∀ (T : ℝ), 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B :=
    avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
      X q x D B hStrict
  have hNatural :
      ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B :=
    avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
      X q x D B hClosed
  exact avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
    X q x D hD B hNatural
