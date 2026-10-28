-- Prove2me | solution 1 for D1Bound5.eisenstein_trace_zero_product
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:36.661239+00:00
-- url     : https://prove2.me/submissions/2292e101-ebd0-47ff-ab21-2d0340ef26d6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5



/-- The product of two purely imaginary Eisenstein integers is the
ordinary integer -3 times the product of their real coordinates. -/
theorem _root_.solution (z w : QuadInt 1 1)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0) :
    z * w + 1 = ((1 - 3 * z.re * w.re : ℤ) : QuadInt 1 1) := by
  have hzi : z.im = -2 * z.re := by omega
  have hwi : w.im = -2 * w.re := by omega
  apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id, hzi, hwi] <;>
    ring







end D1Bound5
end
