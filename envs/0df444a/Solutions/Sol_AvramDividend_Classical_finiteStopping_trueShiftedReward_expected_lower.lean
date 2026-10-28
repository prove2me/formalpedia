-- Prove2me | solution 1 for AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:09:19.941013+00:00
-- url     : https://prove2.me/submissions/f7d0bad9-f46c-4e20-b49e-5f96c0798ee5

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_lower_imported
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

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
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
       let up : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)
       let dn : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)
       if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
      else 0 ∂P) := by
  apply finiteStopping_trueTwoSided_expected_lower_imported
    X τ hτ A hA hAfine hτfine discount hd q upper lower
    (fun ω => if ω ∈ A then discount (τ ω) *
      (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
       let up : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)
       let dn : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)
       if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
      else 0)
  intro ω
  by_cases hAω : ω ∈ A
  · simp only [if_pos hAω]
    have hReward := levy_shifted_trueTwoSided_reward_eq_schedule
      X ω (τ ω) q upper lower
    simpa only using
      (congrArg (fun z : ℝ≥0∞ => discount (τ ω) * z) hReward).symm.le
  · simp [hAω]
