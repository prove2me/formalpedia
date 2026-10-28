-- Prove2me | solution 1 for D1Bound5.QuadInt.four_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:23:32.601018+00:00
-- url     : https://prove2.me/submissions/36886de7-abe1-4962-a6e4-8441a4323cf6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_formula

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}





/-- Equation (integrated-disk), completed-square identity. -/
theorem _root_.solution (z : QuadInt tau nu) :
    4*z.norm = (2*z.re+tau*z.im)^2 + discriminant tau nu*z.im^2 := by
  rw [norm_formula]
  unfold discriminant
  ring











end QuadInt
end D1Bound5
end
