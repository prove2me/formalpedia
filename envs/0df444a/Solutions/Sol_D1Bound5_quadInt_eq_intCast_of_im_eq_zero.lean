-- Prove2me | solution 1 for D1Bound5.quadInt_eq_intCast_of_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:59.71543+00:00
-- url     : https://prove2.me/submissions/a7de04c0-43b1-421e-bb09-dbb58b0f5bd8

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5

/-- An element with zero imaginary coordinate is its ordinary integer
real coordinate. No sign or discriminant hypothesis is needed. -/
theorem _root_.solution {tau nu : ℤ}
    (z : QuadInt tau nu) (him : z.im = 0) :
    z = (z.re : QuadInt tau nu) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_intCast, Int.cast_id]
  · simpa only [QuadraticAlgebra.im_intCast] using him









end D1Bound5
end
