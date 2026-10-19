-- Prove2me | solution 1 for BenfordLaw.leadingDigit_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:43:24.64234+00:00
-- url     : https://prove2.me/submissions/81c8ca44-13f4-483b-b049-90ced78f201d

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

theorem solution (x : ℝ) (hx : x ≠ 0) :
    leadingDigit 2 x = 1 := by
  unfold leadingDigit
  rw [Nat.floor_eq_iff (by positivity)]
  have h0 := Int.fract_nonneg (Real.logb ((2 : ℕ) : ℝ) x)
  have h1 := Int.fract_lt_one (Real.logb ((2 : ℕ) : ℝ) x)
  push_cast
  constructor
  · simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) h0
  · have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
    norm_num at this ⊢
    exact this
