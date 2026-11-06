-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:16:27.72077+00:00
-- url     : https://prove2.me/submissions/7243442a-5bcf-44be-9d25-b45098925b0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hnReal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hSet (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T =
        (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T := by
    rw [← ENNReal.ofReal_natCast n]
    rw [paymentTimes_min_ofReal_eq_inter_Iio_of_pos
      (ruinTime X x D ω) (n : ℝ) hnReal]
  have hCash (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [hSet ω]
  simp_rw [hCash]
