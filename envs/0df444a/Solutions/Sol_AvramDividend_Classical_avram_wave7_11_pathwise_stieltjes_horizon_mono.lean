-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_pathwise_stieltjes_horizon_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:55:12.546396+00:00
-- url     : https://prove2.me/submissions/0c4eeaf2-e501-4f69-a8dc-4d0307640401

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The complete original-path discounted Stieltjes reward increases
    with the finite real observation horizon, including its t=0 atom. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T U : ℝ) (hTU : T ≤ U) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes σ ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  exact ⟨ht.1, le_trans ht.2 hTU⟩
