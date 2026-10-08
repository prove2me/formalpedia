-- Prove2me | solution 1 for ConnesGreen.gammaBracket_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T01:01:30.216989+00:00
-- url     : https://prove2.me/submissions/115a5f1e-8b4c-47b6-81e3-e92b0cf504df

import Mathlib
import Theorems.Thm_ConnesGreen_digamma_re_vertical_minimum
set_option autoImplicit false
open Complex
theorem solution (r : ℝ) : (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi ≤
      (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi := by
  have h := ConnesGreen.digamma_re_vertical_minimum (1 / 4) (by norm_num) (by norm_num) (r / 2)
  have he : ((1 / 4 : ℝ) : ℂ) + I * ((r / 2 : ℝ) : ℂ) = 1 / 4 + I * r / 2 := by push_cast; ring
  rw [he] at h
  norm_num at h
  exact sub_le_sub_right h _

