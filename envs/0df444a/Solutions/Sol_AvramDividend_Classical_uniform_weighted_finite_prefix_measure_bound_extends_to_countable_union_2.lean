-- Prove2me | solution 2 for AvramDividend.Classical.uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:44:36.533142+00:00
-- url     : https://prove2.me/submissions/ae2f62f6-6b31-4835-9bae-6c87d2174964

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Inv
open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (s : ℕ → Set Ω)
    (hs : Monotone s) (hms : ∀ n : ℕ, MeasurableSet (s n))
    (a : ℝ≥0∞)
    (hfinite : ∀ n : ℕ, a * μ (s n) ≤ 1) :
    a * μ (⋃ n, s n) ≤ 1 := by
  rw [hs.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hfinite
