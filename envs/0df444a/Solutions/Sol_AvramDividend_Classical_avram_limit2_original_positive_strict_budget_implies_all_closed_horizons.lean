-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:55:01.238567+00:00
-- url     : https://prove2.me/submissions/09990e91-53ea-4fcb-9285-d65c28757b90

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_later_real_horizon_cash_dominates_closed
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
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hStrict : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B) :
    ∀ (T : ℝ), 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by
  intro T hT
  have hLater : T < T + 1 := by linarith
  have hPositive : 0 < T + 1 := by linarith
  exact
    (avram_limit2_strict_later_real_horizon_cash_dominates_closed
      X q x D T (T + 1) hLater).trans
      (hStrict (T + 1) hPositive)
