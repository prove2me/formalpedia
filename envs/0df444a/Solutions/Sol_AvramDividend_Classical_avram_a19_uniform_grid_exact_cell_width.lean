-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_uniform_grid_exact_cell_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:09:27.171728+00:00
-- url     : https://prove2.me/submissions/9fe4a62d-1f1e-42e9-92ac-b68cf83900f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every physical-grid cell has the exact positive mesh width. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n i : ℕ) :
    (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2) := by
  rw [huniform n (i + 1), huniform n i]
  push_cast
  ring
