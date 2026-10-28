-- Prove2me | solution 1 for AvramDividend.Classical.countable_future_twoSided_exit_clocks_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:29:37.084304+00:00
-- url     : https://prove2.me/submissions/94964af6-c028-4176-b7c9-a56e51c94041

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (τ : ℕ → ℝ≥0) (upper lower : ℝ) :
    Measurable (fun g : ℝ≥0 → ℝ =>
      ⨅ j : ℕ, if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤) ∧
    Measurable (fun g : ℝ≥0 → ℝ =>
      ⨅ j : ℕ, if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤) := by
  constructor
  · refine Measurable.iInf fun j => ?_
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply (τ j)))
      measurable_const measurable_const
  · refine Measurable.iInf fun j => ?_
    exact Measurable.ite (measurableSet_lt (measurable_pi_apply (τ j)) measurable_const)
      measurable_const measurable_const
