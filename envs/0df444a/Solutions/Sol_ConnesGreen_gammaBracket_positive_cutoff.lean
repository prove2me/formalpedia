-- Prove2me | solution 1 for ConnesGreen.gammaBracket_positive_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T01:34:37.09632+00:00
-- url     : https://prove2.me/submissions/e6956070-4a0b-49b1-b398-b546a184a43d

import Mathlib
import Theorems.Thm_ConnesGreen_digamma_stirling_log_abs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex
theorem solution :
    1 ≤ (Complex.digamma (1 / 4 + I * ((2 * Real.exp (6 + |Real.log Real.pi|) : ℝ) : ℂ) / 2)).re - Real.log Real.pi := by 
  let t := Real.exp (6 + |Real.log Real.pi|)
  have ht : 1 ≤ t := Real.one_le_exp (by positivity)
  have htp : 0 < t := Real.exp_pos _
  have hs := ConnesGreen.digamma_stirling_log_abs (a := 1 / 4)
    (by norm_num) (by norm_num) (t := t) (by rw [abs_of_pos htp]; linarith)
  have he : 5 / t ^ 2 ≤ 5 := (div_le_iff₀ (by positivity : 0 < t ^ 2)).mpr (by nlinarith)
  rw [abs_of_pos htp, show Real.log t = 6 + |Real.log Real.pi| from Real.log_exp _] at hs
  have hlow := (abs_le.mp hs).1
  rw [show ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) by norm_num] at hlow
  have hz : (1 / 4 : ℂ) + I * ((2 * Real.exp (6 + |Real.log Real.pi|) : ℝ) : ℂ) / 2 = (1 / 4 : ℂ) + I * (t : ℂ) := by
    dsimp [t]
    push_cast
    ring
  rw [hz]
  linarith [le_abs_self (Real.log Real.pi)]

