-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_closed_horizon_real_cash_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:48:03.865758+00:00
-- url     : https://prove2.me/submissions/28370fca-2d37-4606-b2d7-da7753f7c7b2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_discounted_cash_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- For finite original stopped cash, converting the exact horizon split to
    reals preserves the right-payment atom at the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (ω : Ω)
    (hPaid : MeasurableSet (paymentTimes (ruinTime X x D ω)))
    (hfinite :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hsplit := avram_p3_bv_closed_horizon_discounted_cash_split
    X x D q T ω hPaid
  rw [hsplit]
  have hsum :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
    rwa [hsplit] at hfinite
  exact ENNReal.toReal_add
    (ne_top_of_lt (ENNReal.add_lt_top.mp hsum).1)
    (ne_top_of_lt (ENNReal.add_lt_top.mp hsum).2)
