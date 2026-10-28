-- Prove2me | solution 1 for D1Bound5.trace_zero_tau_zero_product
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:11.751852+00:00
-- url     : https://prove2.me/submissions/9a23f9fa-238d-4030-82e6-9e215c70ab44

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5







/-- Exact product on the imaginary axis in the trace-zero basis. -/
theorem _root_.solution {nu : ℤ} (z w : QuadInt 0 nu)
    (hz : 2 * z.re = 0) (hw : 2 * w.re = 0) :
    z * w + 1 = ((1 - nu * z.im * w.im : ℤ) : QuadInt 0 nu) := by
  have hzr : z.re = 0 := by omega
  have hwr : w.re = 0 := by omega
  apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id, hzr, hwr] <;>
    ring















end D1Bound5
end
