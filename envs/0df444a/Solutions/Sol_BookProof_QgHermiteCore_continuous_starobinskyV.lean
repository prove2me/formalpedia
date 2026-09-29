-- Prove2me | solution 1 for BookProof.QgHermiteCore.continuous_starobinskyV
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:06:50.396817+00:00
-- url     : https://prove2.me/submissions/a1ec2d97-2b3f-4eef-b0be-8c0cfe28bad3

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
set_option autoImplicit false

theorem solution (M alpha : ℝ) :
    Continuous (fun phi : ℝ => M ^ 4 / (16 * alpha) *
      (1 - Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) ^ 2) := by
  fun_prop
#print axioms solution
