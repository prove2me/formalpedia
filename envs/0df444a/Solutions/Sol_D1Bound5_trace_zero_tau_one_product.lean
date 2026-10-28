-- Prove2me | solution 1 for D1Bound5.trace_zero_tau_one_product
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:24.698488+00:00
-- url     : https://prove2.me/submissions/5012a1b5-8b89-43ba-8ce7-361282c04fc6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5















/-- Exact product on the imaginary axis in the trace-one basis. -/
theorem _root_.solution {nu : ℤ} (z w : QuadInt 1 nu)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0) :
    z * w + 1 = ((1 - (4 * nu - 1) * z.re * w.re : ℤ) : QuadInt 1 nu) := by
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
