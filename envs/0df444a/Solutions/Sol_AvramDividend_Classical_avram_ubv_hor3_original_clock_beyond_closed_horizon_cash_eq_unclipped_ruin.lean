-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:32:32.264739+00:00
-- url     : https://prove2.me/submissions/626d0818-2ace-4f4c-9889-3b3d762d73f3

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
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (n : ℕ)
    (hn : 0 < n) (hTn : T < (n : ℝ)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hSet (ω : Ω) :
      (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T =
        paymentTimes (ruinTime X x D ω) ∩ Iic T := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · intro ht
      exact ⟨⟨ht.1, lt_of_le_of_lt ht.2 hTn⟩, ht.2⟩
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
        (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
        X x D q T n hn
    _ = (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
      simp_rw [hSet]
