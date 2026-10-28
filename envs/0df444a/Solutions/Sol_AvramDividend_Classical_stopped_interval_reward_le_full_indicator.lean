-- Prove2me | solution 1 for AvramDividend.Classical.stopped_interval_reward_le_full_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:44:38.128518+00:00
-- url     : https://prove2.me/submissions/98b16810-502a-4ce7-aced-6af36f52ac80

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Nonnegative stopped interval rewards are dominated by the full permitted reward. -/
theorem solution
    (μ : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (q a b : ℝ) :
    (∫⁻ t in S,
      if t ∈ Set.Ioc a b then
        ENNReal.ofReal (Real.exp (-(q * t))) else 0 ∂μ) ≤
    (∫⁻ t,
      if t ∈ S then ENNReal.ofReal (Real.exp (-(q * t))) else 0
      ∂μ) := by
  classical
  calc
    (∫⁻ t in S,
      if t ∈ Set.Ioc a b then
        ENNReal.ofReal (Real.exp (-(q * t))) else 0 ∂μ) ≤
      (∫⁻ t in S,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by
          apply lintegral_mono
          intro t
          by_cases ht : t ∈ Set.Ioc a b
          · simp only [if_pos ht, le_refl]
          · simp only [if_neg ht]
            exact zero_le
    _ = (∫⁻ t,
      if t ∈ S then ENNReal.ofReal (Real.exp (-(q * t))) else 0
      ∂μ) := by
        change
          (∫⁻ t in S, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
          (∫⁻ t, S.indicator
            (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) t ∂μ)
        exact (lintegral_indicator (μ := μ) hS
          (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))).symm
