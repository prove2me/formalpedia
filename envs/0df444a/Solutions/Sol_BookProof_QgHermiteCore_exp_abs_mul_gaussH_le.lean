-- Prove2me | solution 1 for BookProof.QgHermiteCore.exp_abs_mul_gaussH_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:40:06.082996+00:00
-- url     : https://prove2.me/submissions/747bca25-3d49-45cb-a0ea-27b02b5494cc

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (c x : ℝ) :
    Real.exp (c * |x|) * Real.exp (-x ^ 2 / 4) ≤
      Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|x| - 4 * c), sq_abs x]

#print axioms solution
