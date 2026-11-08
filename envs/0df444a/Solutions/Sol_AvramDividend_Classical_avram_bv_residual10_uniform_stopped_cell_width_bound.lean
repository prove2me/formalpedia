-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_uniform_stopped_cell_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:32:08.577999+00:00
-- url     : https://prove2.me/submissions/faf00567-cd1e-4bc2-9143-0391979bb6cc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- A physical uniform cell remains nonnegative and no wider after
clipping both endpoints at any common stopping clock. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (s : ℝ) :
    ∀ n i : ℕ,
      0 ≤ min (u n (i + 1) : ℝ) s - min (u n i : ℝ) s ∧
      min (u n (i + 1) : ℝ) s - min (u n i : ℝ) s ≤
        T / ((n : ℝ) + 2) := by
  intro n i
  have hdelta :
      (u n (i + 1) : ℝ) - (u n i : ℝ) =
        T / ((n : ℝ) + 2) := by
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hmono : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
    nlinarith [div_pos hT hd]
  rcases le_total s (u n i : ℝ) with hsi | his
  · have hsj : s ≤ (u n (i + 1) : ℝ) := le_trans hsi hmono
    rw [min_eq_right hsi, min_eq_right hsj]
    constructor <;> nlinarith [div_pos hT hd]
  · rcases le_total s (u n (i + 1) : ℝ) with hsj | hjs
    · rw [min_eq_left his, min_eq_right hsj]
      constructor <;> nlinarith [hdelta]
    · rw [min_eq_left his, min_eq_left hjs]
      constructor <;> nlinarith [hdelta, div_pos hT hd]
