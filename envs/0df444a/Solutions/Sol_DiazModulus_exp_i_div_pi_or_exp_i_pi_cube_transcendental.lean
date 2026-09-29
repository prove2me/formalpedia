-- Prove2me | solution 1 for DiazModulus.exp_i_div_pi_or_exp_i_pi_cube_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:37:38.737506+00:00
-- url     : https://prove2.me/submissions/a9337528-0f32-4ec1-aace-eec1478198f5

import Mathlib
import Theorems.Thm_DiazModulus_recip_pi_or_pi_cube

/-- The first disjunction of `DiazModulus.recip_pi_or_pi_cube` at `γ = 1`. -/
theorem solution :
    Transcendental ℚ (Complex.exp (Complex.I / ((Real.pi : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3)) := by
  have h := (DiazModulus.recip_pi_or_pi_cube 1 (isAlgebraic_one (R := ℚ) (A := ℂ))
    one_ne_zero).1
  simpa only [mul_one, div_one] using h

#print axioms solution
