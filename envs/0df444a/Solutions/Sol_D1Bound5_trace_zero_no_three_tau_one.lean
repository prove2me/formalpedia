-- Prove2me | solution 1 for D1Bound5.trace_zero_no_three_tau_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:15:33.080992+00:00
-- url     : https://prove2.me/submissions/83934c1a-d050-4554-a374-48dbd4002b00

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_trace_zero_tau_one_compatible_opposite

section
namespace D1Bound5



















/-- Three nonzero trace-zero elements cannot be pairwise compatible
in the trace-one basis when 4*nu-1>1. -/
theorem _root_.solution {nu : ℤ} (hnu : 1 < 4 * nu - 1)
    (x y z : QuadInt 1 nu) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hx : 2 * x.re + x.im = 0) (hy : 2 * y.re + y.im = 0)
    (hz : 2 * z.re + z.im = 0)
    (hxy : ∃ r : QuadInt 1 nu, r * r = x * y + 1)
    (hxz : ∃ r : QuadInt 1 nu, r * r = x * z + 1)
    (hyz : ∃ r : QuadInt 1 nu, r * r = y * z + 1) : False := by
  have h1 := trace_zero_tau_one_compatible_opposite hnu x y hx0 hy0 hx hy hxy
  have h2 := trace_zero_tau_one_compatible_opposite hnu x z hx0 hz0 hx hz hxz
  have h3 := trace_zero_tau_one_compatible_opposite hnu y z hy0 hz0 hy hz hyz
  have hp := mul_pos_of_neg_of_neg h1 h2
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x.re) h3.le
  nlinarith only [hp, hn]



end D1Bound5
end
