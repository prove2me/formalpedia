-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_clock_cash_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:06:37.717266+00:00
-- url     : https://prove2.me/submissions/30ee9534-7dba-4cd9-913d-ea8392c23696

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
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  have hnmReal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hMono :
      (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (m : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    exact ⟨⟨ht.1.1,
      Set.mem_Iio.mpr (lt_of_lt_of_le (Set.mem_Iio.mp ht.1.2) hnmReal)⟩, ht.2⟩
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
        (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq X x D q T n hn
    _ ≤ (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (m : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := hMono
    _ = (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      (avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq X x D q T m hm).symm
