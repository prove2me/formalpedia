-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_canonical_horizon_prefix_mesh_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:56:02.448581+00:00
-- url     : https://prove2.me/submissions/eae497d0-ad79-45eb-a207-5ab407b7fc4e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section

/- The original prefix grid is exactly the n+1-cell source grid
   over the strict horizon T - T/(n+2). -/
theorem solution
    (T : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i, (u n i : ℝ) =
      ((T - T / ((n : ℝ) + 2)) / ((n : ℝ) + 1)) * (i : ℝ) := by
  intro n i
  rw [huniform n i]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring
