-- Prove2me | solution 1 for D1Bound5.tail_error_sum_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:27.874991+00:00
-- url     : https://prove2.me/submissions/5b2d2f30-da5d-4fb0-87bb-5a186ae8eac2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- The real error estimate needed for a regular tail with C>=4.
The variables x,y,z are the moduli of square roots of a,b,c. -/
theorem _root_.solution (x y z er eu ev ew : ℝ)
    (hx : 1 ≤ x) (hy : (12/7 : ℝ) ≤ y) (hz : 2 ≤ z) (hxy : x ≤ y)
    (her : 0 ≤ er) (heu : 0 ≤ eu) (hev : 0 ≤ ev) (_hew : 0 ≤ ew)
    (hr : (39/20 : ℝ)*y*z*er < 1)
    (hu : (9/5 : ℝ)*x*y*eu < 1)
    (hv : (13/7 : ℝ)*x*z*ev < 1)
    (hw : (216/125 : ℝ)*x*z*ew < 1+2*x^2*er) : eu+ev+ew < 1 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hYZ : (24/7 : ℝ) ≤ y*z := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]
  have hr0 : er < (35/234 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hYZ) her]
  have hXZ : 2 ≤ x*z := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz)]
  have hXY : (12/7 : ℝ) ≤ x*y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hcoef : 0 < (216/125 : ℝ)*x*z := by positivity
  by_cases hsmall : x ≤ (8/7 : ℝ)
  · have hu' : eu < (35/108 : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hXY) heu]
    have hv' : ev < (7/26 : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hXZ) hev]
    have hxr : x*er < (20/117 : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) her]
    have hterm : 2*x^2*er < (20/117 : ℝ)*x*z := by
      have h1 := mul_lt_mul_of_pos_left hxr (show 0 < 2*x by positivity)
      have h2 := mul_le_mul_of_nonneg_left hz (show 0 ≤ (20/117 : ℝ)*x by positivity)
      nlinarith only [h1,h2]
    have hw' : ew < (19625/50544 : ℝ) := by
      by_contra hbad
      have hmul := mul_nonneg hcoef.le (sub_nonneg.mpr (le_of_not_gt hbad))
      nlinarith only [hw,hterm,hXZ,hmul]
    linarith
  · have hxlarge : (8/7 : ℝ) ≤ x := le_of_lt (lt_of_not_ge hsmall)
    have hXY' : (96/49 : ℝ) ≤ x*y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxlarge) (sub_nonneg.mpr hy)]
    have hXZ' : (16/7 : ℝ) ≤ x*z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxlarge) (sub_nonneg.mpr hz)]
    have hu' : eu < (245/864 : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hXY') heu]
    have hv' : ev < (49/208 : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hXZ') hev]
    have hxrZ : x*er*z < (20/39 : ℝ) := by
      have h := mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hz0.le her)
      nlinarith only [hr,h]
    have hxr : x*er < (5/39 : ℝ)*z := by
      by_contra hbad
      have hmul := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad)) hz0.le
      nlinarith only [hxrZ, sq_nonneg (z-2), hz, hmul]
    have hterm : 2*x^2*er < (10/39 : ℝ)*x*z := by
      have h := mul_lt_mul_of_pos_left hxr (show 0 < 2*x by positivity)
      nlinarith only [h]
    have hw' : ew < (54125/134784 : ℝ) := by
      by_contra hbad
      have hmul := mul_nonneg hcoef.le (sub_nonneg.mpr (le_of_not_gt hbad))
      nlinarith only [hw,hterm,hXZ',hmul]
    linarith



end D1Bound5
end
