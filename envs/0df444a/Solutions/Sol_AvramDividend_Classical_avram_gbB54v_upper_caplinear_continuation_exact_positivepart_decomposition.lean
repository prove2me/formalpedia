-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54v_upper_caplinear_continuation_exact_positivepart_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:32:51.779469+00:00
-- url     : https://prove2.me/submissions/c1ce09d8-b3f4-42f4-9014-e2d17c52db98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b α z : ℝ) :
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let U : ℝ → ℝ := fun y => if y ≤ b then w y else w b + α * (y - b)
    V z = U z - (α - 1) * max (z - b) 0 := by
  dsimp
  by_cases hz : z ≤ b
  · have hzb : z - b ≤ 0 := sub_nonpos.mpr hz
    simp [hz, max_eq_right hzb]
  · have hzb : 0 ≤ z - b := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hz))
    simp [hz, max_eq_left hzb]
    ring
