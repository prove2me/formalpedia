-- Prove2me | solution 1 for D1Bound5.eisenstein_trace_zero_compatible_opposite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:10.533888+00:00
-- url     : https://prove2.me/submissions/02344120-5c55-40a6-888e-45b7ea13d1f4

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions
import Theorems.Thm_D1Bound5_eisenstein_trace_zero_product

section
namespace D1Bound5

/-- A nonzero purely imaginary Eisenstein integer has nonzero real
coordinate in the basis omega^2-omega+1=0. -/
theorem eisenstein_trace_zero_re_ne_zero (z : QuadInt 1 1)
    (hz : z ≠ 0) (htrace : 2 * z.re + z.im = 0) : z.re ≠ 0 := by
  intro hre
  have him : z.im = 0 := by omega
  apply hz
  apply QuadraticAlgebra.ext
  · simpa only [QuadraticAlgebra.re_zero] using hre
  · simpa only [QuadraticAlgebra.im_zero] using him



/-- Two compatible nonzero purely imaginary Eisenstein integers must
lie on opposite half-axes. The zero-root case is included in the input. -/
theorem _root_.solution
    (z w : QuadInt 1 1) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0)
    (hsquare : ∃ r : QuadInt 1 1, r * r = z * w + 1) :
    z.re * w.re < 0 := by
  have hzn := eisenstein_trace_zero_re_ne_zero z hz0 hz
  have hwn := eisenstein_trace_zero_re_ne_zero w hw0 hw
  have hprod0 : z.re * w.re ≠ 0 := mul_ne_zero hzn hwn
  by_contra hneg
  have hpos : 0 < z.re * w.re := by omega
  have hm : 1 - 3 * z.re * w.re < 0 := by nlinarith only [hpos]
  have hsquare' : ∃ r : QuadInt 1 1,
      r * r = ((1 - 3 * z.re * w.re : ℤ) : QuadInt 1 1) := by
    simpa only [eisenstein_trace_zero_product z w hz hw] using hsquare
  obtain ⟨n, hn⟩ := negative_integer_square_trace_one (nu := 1) hm hsquare'
  norm_num at hn
  ring_nf at hn
  omega





end D1Bound5
end
