-- Prove2me | solution 1 for AvramDividend.Classical.avram_a34_original_finitecap_ruin_negative_crossing_positive_caplinear_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:47:54.05946+00:00
-- url     : https://prove2.me/submissions/5ab9ceee-70df-42dd-ad1e-13dfe92a92d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (y r : ℝ) (hy : 0 ≤ y) (hyc : y ≤ c)
    (hwy : 0 ≤ w y) (hneg : y + r < 0) :
    max ((if y + r ≤ c then w (y + r)
      else w c + (y + r - c)) - w y) 0 = 0  := by
  have hcap : y + r ≤ c := by linarith
  rw [if_pos hcap, hw_neg (y + r) hneg]
  have hn : (0 : ℝ) - w y ≤ 0 := by linarith
  exact max_eq_right hn
