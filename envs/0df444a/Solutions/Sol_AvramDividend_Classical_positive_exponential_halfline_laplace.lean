-- Prove2me | solution 1 for AvramDividend.Classical.positive_exponential_halfline_laplace
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:17:57.552935+00:00
-- url     : https://prove2.me/submissions/b80511a6-3de7-49f6-8ae0-aa4a1759838f

import Mathlib

open MeasureTheory Set Real
open scoped NNReal ENNReal

open MeasureTheory Set Real in
theorem solution (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-θ * x))) =
      ENNReal.ofReal (1 / θ) := by
  have ha : -θ < 0 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha 0)
    (ae_of_all _ (fun x => (Real.exp_pos _).le)),
    integral_exp_mul_Ioi ha 0]
  congr 1
  rw [mul_zero, Real.exp_zero]
  field_simp
