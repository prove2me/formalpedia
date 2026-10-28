-- Prove2me | solution 1 for D1Bound5.QuadInt.norm_formula
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:51.246168+00:00
-- url     : https://prove2.me/submissions/c0226936-4710-4e4c-b4d8-bf6c6c6ec04f

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}



/-- Equation (integrated-disk), first identity. -/
theorem _root_.solution (z : QuadInt tau nu) :
    z.norm = z.re^2 + tau*z.re*z.im + nu*z.im^2 := by
  rw [QuadraticAlgebra.norm_def]
  ring













end QuadInt
end D1Bound5
end
