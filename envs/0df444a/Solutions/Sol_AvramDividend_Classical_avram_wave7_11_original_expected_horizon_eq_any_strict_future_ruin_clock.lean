-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:17:34.054643+00:00
-- url     : https://prove2.me/submissions/cdbac3c8-59b9-4b2c-8608-058eebef4f4f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any deterministic truncation clock strictly later than a finite
    real horizon gives exactly the same original-law Stieltjes dividend value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (η : ℝ≥0∞) (hFuture : ENNReal.ofReal T < η) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) η) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_congr
  intro ω
  rw [avram_wave7_11_strict_future_clock_preserves_finite_payment_set
    (ruinTime X x D ω) η T hFuture]
