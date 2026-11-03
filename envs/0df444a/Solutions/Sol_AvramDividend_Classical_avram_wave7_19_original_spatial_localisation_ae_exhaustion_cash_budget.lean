-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:00:10.158972+00:00
-- url     : https://prove2.me/submissions/f8c0dde5-0d94-4a93-8083-13ea28b35daa

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original-source ENNReal cash bound after an almost-surely exhaustive increasing spatial localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ k : ℕ, Measurable (LocalCash k))
    (hLocalMon : ∀ ω : Ω, Monotone (fun k : ℕ => LocalCash k ω))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ⨆ k : ℕ, LocalCash k ω)
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ, (∫⁻ ω, LocalCash k ω ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
      budget := by
  have hMon : Monotone LocalCash := by
    intro k l hkl ω
    exact hLocalMon ω hkl
  calc
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
        ∫⁻ ω, ⨆ k : ℕ, LocalCash k ω ∂P :=
      lintegral_mono_ae hExhaust
    _ = ⨆ k : ℕ, (∫⁻ ω, LocalCash k ω ∂P) :=
      lintegral_iSup hLocalMeas hMon
    _ ≤ budget := iSup_le hBound
