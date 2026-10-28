-- Prove2me | solution 1 for AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:24:17.229226+00:00
-- url     : https://prove2.me/submissions/a6ef9123-28c1-42c7-8d58-ac4a785cd95c

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_upper
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

/-- Exact stopped strong-Markov factorisation for the shifted two-sided exit reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A) (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
       let up : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)
       let dn : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)
       if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
      else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by
  exact le_antisymm
    (finiteStopping_trueShiftedReward_expected_upper
      X τ hτ A hA hAfine hτfine discount hd q upper lower)
    (finiteStopping_trueShiftedReward_expected_lower
      X τ hτ A hA hAfine hτfine discount hd q upper lower)
