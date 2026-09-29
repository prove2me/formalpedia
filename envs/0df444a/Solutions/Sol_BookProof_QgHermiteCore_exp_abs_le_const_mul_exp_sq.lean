-- Prove2me | solution 1 for BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:06:48.173849+00:00
-- url     : https://prove2.me/submissions/9b6a0479-9664-423c-b38b-c36607e9a59c

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem solution (c x : ℝ) :
    Real.exp (c * |x|) ≤ Real.exp (2 * c ^ 2) * Real.exp (x ^ 2 / 8) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|x| - 4 * c), sq_abs x]
#print axioms solution
