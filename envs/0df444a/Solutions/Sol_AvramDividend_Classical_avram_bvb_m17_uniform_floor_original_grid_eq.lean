-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_m17_uniform_floor_original_grid_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:23:46.410407+00:00
-- url     : https://prove2.me/submissions/83a524d2-781e-41e2-b385-9733ccd7a2cb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (r : ℝ) :
    u n ⌊(r / T) * ((n : ℝ) + 2)⌋₊ =
      Real.toNNReal
        (T * (⌊(r / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2)) := by
  let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
  have hi : 0 ≤ T * (i : ℝ) / ((n : ℝ) + 2) := by positivity
  apply Subtype.ext
  change (u n i : ℝ) =
    ((Real.toNNReal (T * (i : ℝ) / ((n : ℝ) + 2)) : ℝ≥0) : ℝ)
  rw [huniform n i, Real.coe_toNNReal _ hi]
