-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:54:29.96475+00:00
-- url     : https://prove2.me/submissions/c68c2bbc-e442-4f5b-a9cd-24610ab62700

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
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
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hBound :
      (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, Set.mem_Iic.mpr (le_of_lt ht.1.2)⟩
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
        (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
        X x D q T n hn
    _ ≤ (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := hBound
    _ = (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      (avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
        X x D q (n : ℝ) n hn).symm
