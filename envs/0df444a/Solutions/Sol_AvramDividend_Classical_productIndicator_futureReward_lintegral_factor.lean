-- Prove2me | solution 1 for AvramDividend.Classical.productIndicator_futureReward_lintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:33:23.869106+00:00
-- url     : https://prove2.me/submissions/0c31a1c8-665a-4d05-bdaa-04c42077f981

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Product integration of a stopped-event indicator and an independent future payoff. -/
theorem solution
    {E : Type*} [MeasurableSpace E]
    (μ : Measure ℝ) (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ h : ℝ, ∫⁻ y : E,
      (if h = 1 then g y else 0) ∂ν ∂μ) =
      μ ({1} : Set ℝ) * (∫⁻ y, g y ∂ν) := by
  let c : ℝ≥0∞ := ∫⁻ y, g y ∂ν
  have hinner (h : ℝ) :
      (∫⁻ y : E, (if h = 1 then g y else 0) ∂ν) =
        if h = 1 then c else 0 := by
    by_cases hh : h = 1
    · simp [hh, c]
    · simp [hh]
  simp_rw [hinner]
  have hfun :
      (fun h : ℝ => if h = 1 then c else 0) =
        Set.indicator ({1} : Set ℝ) (fun _ => c) := by
    funext h
    by_cases hh : h = 1
    · simp [Set.indicator, hh]
    · simp [Set.indicator, hh]
  change (∫⁻ h : ℝ, (if h = 1 then c else 0) ∂μ) =
    μ ({1} : Set ℝ) * c
  rw [hfun]
  rw [lintegral_indicator (measurableSet_singleton (1 : ℝ))]
  simp [lintegral_const, mul_comm]