-- Prove2me | solution 1 for D1Bound5.full_ring_descent_denominator_norm_sq_ge_seven
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:26.901987+00:00
-- url     : https://prove2.me/submissions/4b10e32a-18bb-4d38-b539-8d4b51b0a558

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
import Theorems.Thm_D1Bound5_discrete_two_square_sub_one_norm_sq_ge_seven
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5





/-- The denominator estimate needed for small-pair descent holds in the
full integer ring. The zero radicand is explicitly the exceptional case;
no smallness, strict norm ordering, or unit classification is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b r : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a * b + 1 ≠ 0) (hr : r ^ 2 = a * b + 1) :
    7 ≤ ‖2 * phi (a : K) * phi (b : K) + 1‖ ^ 2 := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hr0 : r ≠ 0 := by
    intro h
    apply hab
    simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hr.symm
  have hr1 : r ^ 2 ≠ 1 := by
    intro h
    apply mul_ne_zero ha hb
    linear_combination -hr + h
  have hbound := discrete_two_square_sub_one_norm_sq_ge_seven f
    (fun x hx => one_le_norm_integer hK phi hx) r hr0 hr1
  have hs : (f r) ^ 2 = f a * f b + 1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hr
  have he : (2 : ℂ) * (f r) ^ 2 - 1 = 2 * f a * f b + 1 := by
    rw [hs]
    ring
  rw [he] at hbound
  exact hbound

end D1Bound5
end
