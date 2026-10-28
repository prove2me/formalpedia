-- Prove2me | solution 1 for D1Bound5.monic_quadratic_neg_between
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:03.689432+00:00
-- url     : https://prove2.me/submissions/fd85c457-f83a-4b5c-94a9-51ec24c12e51

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5





/-- Strict negativity of a monic quadratic on a closed interval from its
two endpoint values. This includes equality at either endpoint. -/
theorem _root_.solution (l u x b c : ℝ) (hlu : l < u)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : l^2+b*l+c < 0) (hu : u^2+b*u+c < 0) : x^2+b*x+c < 0 := by
  by_cases hxl : x = l
  · simpa only [hxl] using hl
  have hlxp : 0 < x-l := sub_pos.mpr (lt_of_le_of_ne hlx (Ne.symm hxl))
  have hlup : 0 < u-l := sub_pos.mpr hlu
  have hxun : 0 ≤ u-x := sub_nonneg.mpr hxu
  have h1 := mul_nonpos_of_nonneg_of_nonpos hxun hl.le
  have h2 := mul_neg_of_pos_of_neg hlxp hu
  have h3 := mul_nonneg (mul_nonneg hlup.le hlxp.le) hxun
  have hid : (u-l)*(x^2+b*x+c) =
      (u-x)*(l^2+b*l+c)+(x-l)*(u^2+b*u+c)-(u-l)*(x-l)*(u-x) := by ring
  have hp : (u-l)*(x^2+b*x+c) < 0 := by nlinarith only [hid, h1, h2, h3]
  by_contra h
  have hn := mul_nonneg hlup.le (le_of_not_gt h)
  linarith







end D1Bound5
end
