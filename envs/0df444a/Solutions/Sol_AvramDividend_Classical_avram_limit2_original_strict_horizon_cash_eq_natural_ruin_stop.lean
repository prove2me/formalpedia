-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:14:59.200912+00:00
-- url     : https://prove2.me/submissions/ebe568f3-c85e-4347-85f0-fc788205af98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  have hCash (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [paymentTimes_min_ofReal_eq_inter_Iio_of_pos (ruinTime X x D ω) T hT]
  simp_rw [hCash]
