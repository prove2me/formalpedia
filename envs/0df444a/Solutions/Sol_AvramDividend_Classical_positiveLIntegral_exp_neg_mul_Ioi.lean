-- Prove2me | solution 1 for AvramDividend.Classical.positiveLIntegral_exp_neg_mul_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:35:31.253993+00:00
-- url     : https://prove2.me/submissions/b9cc1f0b-bae6-452a-afb5-76e01aace296

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem solution (s z : ℝ) (hs : 0 < s) :
    (∫⁻ x : ℝ in Ioi z, ENNReal.ofReal (Real.exp (-s * x))) =
      ENNReal.ofReal (Real.exp (-s * z) / s) := by
  have hint : IntegrableOn (fun x : ℝ => Real.exp ((-s) * x)) (Ioi z) :=
    integrableOn_exp_mul_Ioi (a := -s) (by linarith) z
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi z)] (fun x : ℝ => Real.exp ((-s) * x)) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_exp_mul_Ioi (a := -s) (by linarith) z]
  simp [neg_mul]
