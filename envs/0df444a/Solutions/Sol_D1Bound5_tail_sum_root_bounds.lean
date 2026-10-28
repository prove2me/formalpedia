-- Prove2me | solution 1 for D1Bound5.tail_sum_root_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:33.272554+00:00
-- url     : https://prove2.me/submissions/6bf54333-084c-4b7d-8c17-84f2fb3c85ef

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5



/-- The tail perturbation also bounds the modulus of beta+gamma away
from zero, and leaves enough room for a second square-root perturbation. -/
theorem _root_.solution (x y z p er : ℝ)
    (hx : 1 ≤ x) (hy : (12/7 : ℝ) ≤ y) (hz : 2 ≤ z)
    (hp : 0 ≤ p) (her : 0 ≤ er) (hr : (39/20 : ℝ)*y*z*er < 1)
    (horder : z^2 ≤ p^2+2*er) :
    (24/25 : ℝ)*z < p ∧ 1+2*x^2*er < (9/25 : ℝ)*(x*p)^2 := by
  have hYZ : (24/7 : ℝ) ≤ y*z := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]
  have hr0 : er < (35/234 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hYZ) her]
  have hp2 : (12/13 : ℝ)*z^2 < p^2 := by
    nlinarith [sq_nonneg (z-2)]
  constructor
  · nlinarith [sq_nonneg (p-(24/25 : ℝ)*z)]
  · have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
    have hm1 := mul_lt_mul_of_pos_left hr0 (show 0 < x^2 by positivity)
    have hm2 := mul_lt_mul_of_pos_left hp2 (show 0 < x^2 by positivity)
    have hz2 : 4 ≤ z^2 := by nlinarith [sq_nonneg (z-2)]
    have hm3 := mul_le_mul_of_nonneg_left hz2 (sq_nonneg x)
    nlinarith only [hm1,hm2,hm3,hx2]

end D1Bound5
end
