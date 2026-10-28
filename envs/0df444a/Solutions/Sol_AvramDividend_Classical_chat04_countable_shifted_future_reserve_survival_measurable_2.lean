-- Prove2me | solution 2 for AvramDividend.Classical.chat04_countable_shifted_future_reserve_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:27:09.934798+00:00
-- url     : https://prove2.me/submissions/34e7bc28-d83d-4924-b8ae-33d7e44e0cf4

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} := by
  have e : {z : ℝ × (ℝ≥0 → ℝ) | ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} =
      ⋂ j : ℕ, {z : ℝ × (ℝ≥0 → ℝ) | τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} := by
    ext z; simp
  rw [e]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : τ j ≤ T
  · simp only [hj, true_implies]
    exact measurableSet_le measurable_const
      (measurable_fst.add ((measurable_pi_apply (τ j)).comp measurable_snd))
  · simp [hj]
