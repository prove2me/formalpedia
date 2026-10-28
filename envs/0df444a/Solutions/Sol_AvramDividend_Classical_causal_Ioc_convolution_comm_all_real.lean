-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_convolution_comm_all_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:45:57.056512+00:00
-- url     : https://prove2.me/submissions/d8a25b00-d236-493b-90c8-21269fe70dfa

import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (f g : ℝ → ℝ) (x : ℝ) :
    (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) =
      ∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume := by 
  rcases le_or_gt 0 x with hx | hx
  · rw [← intervalIntegral.integral_of_le hx, ← intervalIntegral.integral_of_le hx]
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := x)
      (fun s => g s * f (x - s)) x
    simp only [sub_self, sub_zero, sub_sub_cancel] at this
    rw [← this]
    congr 1; ext s; ring
  · rw [Ioc_eq_empty (by linarith)]
    simp
