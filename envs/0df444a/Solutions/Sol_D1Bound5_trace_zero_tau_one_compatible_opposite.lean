-- Prove2me | solution 1 for D1Bound5.trace_zero_tau_one_compatible_opposite
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:56.549995+00:00
-- url     : https://prove2.me/submissions/c0c01999-cd24-46df-ae94-410ec03eee4d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions
import Theorems.Thm_D1Bound5_trace_zero_tau_one_product

section
namespace D1Bound5

private theorem trace_axis_one_sub_mul_neg (d p : ℤ) (hd : 1 < d) (hp : 0 < p) :
    1 - d * p < 0 := by
  have hp1 : 1 ≤ p := by omega
  have hd0 : 0 ≤ d := by omega
  have hmul := mul_le_mul_of_nonneg_left hp1 hd0
  nlinarith only [hd, hmul]

private theorem trace_axis_one_sub_mul_ne_neg_square (d p n : ℤ) (hd : 1 < d)
    (h : 1 - d * p = -d * n ^ 2) : False := by
  have hdiv : d ∣ (1 : ℤ) := ⟨p - n ^ 2, by nlinarith only [h]⟩
  have hle : d ≤ 1 := Int.le_of_dvd (by norm_num) hdiv
  omega









/-- Nonzero trace-zero elements in the trace-one basis have nonzero
real coordinate. -/
theorem trace_zero_tau_one_re_ne_zero {nu : ℤ} (z : QuadInt 1 nu)
    (hz0 : z ≠ 0) (hz : 2 * z.re + z.im = 0) : z.re ≠ 0 := by
  intro hre
  have him : z.im = 0 := by omega
  apply hz0
  apply QuadraticAlgebra.ext
  · simpa only [QuadraticAlgebra.re_zero] using hre
  · simpa only [QuadraticAlgebra.im_zero] using him



/-- Two compatible nonzero trace-zero elements in a trace-one basis
have real coordinates of opposite signs. -/
theorem _root_.solution {nu : ℤ} (hnu : 1 < 4 * nu - 1)
    (z w : QuadInt 1 nu) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0)
    (hsquare : ∃ r : QuadInt 1 nu, r * r = z * w + 1) :
    z.re * w.re < 0 := by
  have hzn := trace_zero_tau_one_re_ne_zero z hz0 hz
  have hwn := trace_zero_tau_one_re_ne_zero w hw0 hw
  have hprod0 : z.re * w.re ≠ 0 := mul_ne_zero hzn hwn
  by_contra hneg
  have hpos : 0 < z.re * w.re := by omega
  have hm : 1 - (4 * nu - 1) * z.re * w.re < 0 := by
    simpa only [mul_assoc] using
      trace_axis_one_sub_mul_neg (4 * nu - 1) (z.re * w.re) hnu hpos
  have hsquare' : ∃ r : QuadInt 1 nu,
      r * r = ((1 - (4 * nu - 1) * z.re * w.re : ℤ) : QuadInt 1 nu) := by
    simpa only [trace_zero_tau_one_product z w hz hw] using hsquare
  obtain ⟨n, hn⟩ := negative_integer_square_trace_one hm hsquare'
  apply trace_axis_one_sub_mul_ne_neg_square (4 * nu - 1) (z.re * w.re) n hnu
  simpa only [mul_assoc] using hn





end D1Bound5
end
