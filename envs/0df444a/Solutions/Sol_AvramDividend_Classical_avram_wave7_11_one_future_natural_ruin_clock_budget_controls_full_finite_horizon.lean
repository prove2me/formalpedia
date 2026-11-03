-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:22:19.829219+00:00
-- url     : https://prove2.me/submissions/cb264deb-027b-498d-a9c2-5e1649a6ff2f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- One bounded original ruin-clock estimate is sufficient at each
    fixed finite T whenever the chosen natural clock exceeds T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (n : ℕ) (hT : 0 ≤ T) (hFuture : T < (n : ℝ))
    (b : ℝ≥0∞)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b := by
  have hENN : ENNReal.ofReal T < (n : ℝ≥0∞) := by
    have hR : ENNReal.ofReal T < ENNReal.ofReal (n : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT).2 hFuture
    simpa only [ENNReal.ofReal_natCast] using hR
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
          avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
            X x D q T (n : ℝ≥0∞) hENN
    _ ≤ b := hBudget