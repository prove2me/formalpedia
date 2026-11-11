-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_piecewisePath_increment_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:39:18.838672+00:00
-- url     : https://prove2.me/submissions/db084566-22db-4f28-b2d3-4e7708961504

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_jumpCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Finset
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (b : ℝ) (T Y : ℕ → ℝ) (s t : ℝ)
    (hcount : LevyFoundations.jumpCount T s ≤ LevyFoundations.jumpCount T t) :
    LevyFoundations.piecewisePath 0 b T Y t -
        LevyFoundations.piecewisePath 0 b T Y s =
      b * (t - s) +
        ∑ n ∈ Finset.Ico (LevyFoundations.jumpCount T s)
          (LevyFoundations.jumpCount T t), Y n := by
  have hsum := Finset.sum_Ico_eq_sub Y hcount
  simp only [LevyFoundations.piecewisePath]
  rw [hsum]
  ring
