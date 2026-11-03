-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_discounted_stieltjes_horizon_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:01:22.893252+00:00
-- url     : https://prove2.me/submissions/fb0e99e1-9d5c-4cb9-ad6d-dc5ce5b81dea

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Enlarging the deterministic horizon cannot reduce a nonnegative
    original-source discounted Stieltjes dividend integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞) (q T U : ℝ)
    (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply MeasureTheory.lintegral_mono
  intro ω
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  exact ⟨ht.1, le_trans ht.2 hTU⟩
