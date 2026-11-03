-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_arbitrary_horizon_cash_le_source_ruin_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:08:38.871781+00:00
-- url     : https://prove2.me/submissions/d2a1b4e6-bf74-4218-8305-53b540ae6291

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_clock_horizon_cash_le_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_source_ruin_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  exact
    (avram_wave7_08_positive_clock_horizon_cash_le_clock X q x D n hn T).trans
      (avram_wave7_08_truncated_cash_le_source_ruin_clock X q x D n hn)
