-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:53:22.478606+00:00
-- url     : https://prove2.me/submissions/cf546fa5-ec10-41c2-83b4-dcbbdbac6365

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A strictly positive ruin clock excludes precisely its own right-payment
atom from original stopped Cash while retaining the time-zero payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hPos : 0 < τ ω)
    (hRuin : ruinTime X x D ω = (τ ω : ℝ≥0∞)) :
    Cash ω =
      (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  have hDomain :
      paymentTimes (τ ω : ℝ≥0∞) ∩ Iic (τ ω : ℝ) =
        Ico (0 : ℝ) (τ ω : ℝ) := by
    simpa only [lt_irrefl, if_false] using
      (avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
        (τ ω) (τ ω) hPos)
  calc
    Cash ω =
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := hCash ω
    _ = (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by
          rw [hRuin, hDomain]