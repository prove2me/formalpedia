-- Prove2me | solution 1 for AvramDividend.Classical.bounded_survival_deficit_indicator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:17:08.008765+00:00
-- url     : https://prove2.me/submissions/1f5a2697-beee-4cec-bed7-f80b6df07225

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (E : Set Ω) (D : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hMeas : AEStronglyMeasurable (E.indicator D) P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hBound : ∀ ω ∈ E, D ω ≤ C) :
    Integrable (E.indicator D) P := by
  refine Integrable.of_bound hMeas C ?_
  filter_upwards [hNonneg] with ω hω
  by_cases h : ω ∈ E
  · rw [indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg hω]; exact hBound ω h
  · rw [indicator_of_notMem h]; simpa using hC
