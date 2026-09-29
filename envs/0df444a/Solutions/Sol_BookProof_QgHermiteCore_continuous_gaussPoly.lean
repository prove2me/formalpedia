-- Prove2me | solution 1 for BookProof.QgHermiteCore.continuous_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:06:49.657539+00:00
-- url     : https://prove2.me/submissions/c5682e63-747a-40c7-b35f-d2a7858ec686

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp
set_option autoImplicit false

theorem solution (p : Polynomial ℝ) :
    Continuous (fun x : ℝ => p.eval x * Real.exp (-x ^ 2 / 4)) := by
  fun_prop
#print axioms solution
