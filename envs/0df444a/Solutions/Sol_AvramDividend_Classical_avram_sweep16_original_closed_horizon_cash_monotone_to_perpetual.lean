-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_closed_horizon_cash_monotone_to_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:52:58.997206+00:00
-- url     : https://prove2.me/submissions/1e844528-a9c6-43f2-8ef4-c82c05ee4518

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_window_cash_le_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T U : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic U,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ∧
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by
  constructor
  · apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hTU⟩
  · exact avram_sweep16_original_closed_window_cash_le_dividendValue X q x U D
