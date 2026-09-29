-- Prove2me | solution 1 for BookProof.QgHermiteCore.continuous_scalaronSectorPotential
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:11:43.091042+00:00
-- url     : https://prove2.me/submissions/992f1a64-60ac-40be-be2a-88e24194215d

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp
set_option autoImplicit false

theorem solution (M alpha : ℝ) (V3 : Polynomial ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 2) => V3.eval (x 0) +
      M ^ 4 / (16 * alpha) * (1 - Real.exp (-(Real.sqrt (2 / 3)) * x 1 / M)) ^ 2) := by
  fun_prop
#print axioms solution
