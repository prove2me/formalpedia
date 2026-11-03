-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_ubv_ruin_clock_outer_mct_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:55:40.197513+00:00
-- url     : https://prove2.me/submissions/4d22dcb9-a9af-479b-bc8b-b8e3168c7777

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite source-clock cash estimates imply the full cash bound by MCT. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω => (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))))
    (hMono : Monotone (fun n : ℕ => fun ω : Ω => (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))))
    (hLimit : ∀ ω : Ω, (⨆ n : ℕ, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hBudget : ∀ n : ℕ, (∫⁻ ω, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
  classical
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  have hm : ∀ n, Measurable (F n) := hMeas
  have hmon : Monotone F := hMono
  have hfun :
      (fun ω : Ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) = (fun ω => ⨆ n : ℕ, F n ω) := by
    funext ω
    exact (hLimit ω).symm
  calc
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)
        = ∫⁻ ω, (⨆ n : ℕ, F n ω) ∂P := by
            exact congrArg (fun g : Ω → ℝ≥0∞ => ∫⁻ ω, g ω ∂P) hfun
    _ = ⨆ n : ℕ, ∫⁻ ω, F n ω ∂P := MeasureTheory.lintegral_iSup hm hmon
    _ ≤ B := iSup_le (fun n => hBudget n)
