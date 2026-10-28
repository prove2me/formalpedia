-- Prove2me | solution 1 for D1Bound5.eisenstein_no_three_trace_zero_extensions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:07:38.635175+00:00
-- url     : https://prove2.me/submissions/5caaadec-9c22-4e3d-96d4-fd381663ba88

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_eisenstein_trace_zero_compatible_opposite

section
namespace D1Bound5







/-- Three nonzero imaginary Eisenstein integers cannot be pairwise
compatible. This arithmetic endpoint is independent of any coordinate
classification or Pell/descent completeness premise. -/
theorem _root_.solution
    (x y z : QuadInt 1 1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hx : 2 * x.re + x.im = 0) (hy : 2 * y.re + y.im = 0)
    (hz : 2 * z.re + z.im = 0)
    (hxy : ∃ r : QuadInt 1 1, r * r = x * y + 1)
    (hxz : ∃ r : QuadInt 1 1, r * r = x * z + 1)
    (hyz : ∃ r : QuadInt 1 1, r * r = y * z + 1) : False := by
  have h1 := eisenstein_trace_zero_compatible_opposite x y hx0 hy0 hx hy hxy
  have h2 := eisenstein_trace_zero_compatible_opposite x z hx0 hz0 hx hz hxz
  have h3 := eisenstein_trace_zero_compatible_opposite y z hy0 hz0 hy hz hyz
  have hp := mul_pos_of_neg_of_neg h1 h2
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x.re) h3.le
  nlinarith only [hp, hn]



end D1Bound5
end
