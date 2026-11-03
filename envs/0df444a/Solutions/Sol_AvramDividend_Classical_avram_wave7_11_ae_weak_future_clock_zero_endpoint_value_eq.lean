-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_ae_weak_future_clock_zero_endpoint_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:16:59.358436+00:00
-- url     : https://prove2.me/submissions/14a87e01-37af-42b5-9a88-d013fe3d4c84

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For almost surely weakly future clocks, the only obstruction to
    full horizon value equality is the original survivor endpoint cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (hT : 0 < T)
    (η : Ω → ℝ≥0∞)
    (hFuture : ∀ᵐ ω ∂P, ENNReal.ofReal T ≤ η ω)
    (hZeroAtom : ∀ᵐ ω ∂P,
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_congr_ae
  filter_upwards [hFuture, hZeroAtom] with ω hω ha
  have hpath :=
    avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
      D ω (ruinTime X x D ω) (η ω) q T hT hω
  by_cases heq : η ω = ENNReal.ofReal T
  · simpa only [if_pos heq, if_true, ha, add_zero] using hpath
  · simpa only [if_neg heq, add_zero] using hpath
