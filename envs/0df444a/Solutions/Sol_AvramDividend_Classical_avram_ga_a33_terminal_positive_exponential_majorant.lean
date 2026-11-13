-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a33_terminal_positive_exponential_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:44:27.98727+00:00
-- url     : https://prove2.me/submissions/a9a6eac2-9e71-4b49-8c20-ef53837ea726

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_discounted_terminal_positive_part_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (q theta K L : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (t : ℝ≥0) (a y z : ℝ)
    (hLower : -L ≤ y)
    (hUpper : a ≤ K * Real.exp (theta * z)) :
    max (Real.exp (-(q * (t : ℝ))) * (a - y)) 0 ≤
      K * Real.exp (theta * z) + L := by
  have hDiscount :=
    avram_ga_a27_discounted_terminal_positive_part_le q hq t a y
  have hPos : 0 ≤ K * Real.exp (theta * z) :=
    mul_nonneg hK (le_of_lt (Real.exp_pos _))
  have hA : max a 0 ≤ K * Real.exp (theta * z) :=
    max_le hUpper hPos
  have hY : max (-y) 0 ≤ L :=
    max_le (by linarith) hL
  exact hDiscount.trans (add_le_add hA hY)
