-- Prove2me | solution 2 for AvramDividend.Classical.avram_sweep16_original_closed_horizon_cash_monotone_to_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:54:21.655661+00:00
-- url     : https://prove2.me/submissions/273b0794-8f0c-4a74-b45d-e7a61ca61b2a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_closed_window_cash_le_dividendValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  have hsets (ω : Ω) :
      paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic U := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hTU⟩
  constructor
  · apply lintegral_mono
    intro ω
    exact lintegral_mono_set (hsets ω)
  · exact avram_sweep16_original_closed_window_cash_le_dividendValue
      X q x U D
