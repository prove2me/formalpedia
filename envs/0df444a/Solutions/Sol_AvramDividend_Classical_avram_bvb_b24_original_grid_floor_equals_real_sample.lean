-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b24_original_grid_floor_equals_real_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:34:57.020201+00:00
-- url     : https://prove2.me/submissions/1c9ad99f-8b36-469d-a7f2-e2c757ac0311

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual source uniform grid at the real floor index equals its NNReal floor sample. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
       (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (t : ℝ) :
    u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ =
      Real.toNNReal
        (T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2)) := by
  have hnonneg : 0 ≤
      T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
        ((n : ℝ) + 2) := by
    positivity
  apply NNReal.eq
  rw [huniform n ⌊(t / T) * ((n : ℝ) + 2)⌋₊]
  simp [Real.coe_toNNReal, hnonneg]
