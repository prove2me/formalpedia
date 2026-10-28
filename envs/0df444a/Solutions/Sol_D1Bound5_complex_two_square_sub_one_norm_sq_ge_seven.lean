-- Prove2me | solution 1 for D1Bound5.complex_two_square_sub_one_norm_sq_ge_seven
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:40.821748+00:00
-- url     : https://prove2.me/submissions/e7c8fbd4-439b-4f48-8b62-c4c9556f562f

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

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Three discrete-distance bounds suffice for the hyperbolic denominator
estimate. No classification of imaginary-quadratic units is needed. -/
theorem _root_.solution
    (r : ℂ) (hr : 1 ≤ ‖r‖) (hp : 1 ≤ ‖r + 1‖) (hm : 1 ≤ ‖r - 1‖) :
    7 ≤ ‖(2 : ℂ) * r ^ 2 - 1‖ ^ 2 := by
  have hn : 1 ≤ ‖r‖ ^ 2 := by nlinarith [sq_nonneg (‖r‖ - 1)]
  have hp2 : 1 ≤ ‖r + 1‖ ^ 2 := by nlinarith [sq_nonneg (‖r + 1‖ - 1)]
  have hm2 : 1 ≤ ‖r - 1‖ ^ 2 := by nlinarith [sq_nonneg (‖r - 1‖ - 1)]
  have hplus : ‖r + 1‖ ^ 2 = ‖r‖ ^ 2 + 1 + 2 * r.re := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    <;> ring
  have hminus : ‖r - 1‖ ^ 2 = ‖r‖ ^ 2 + 1 - 2 * r.re := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    <;> ring
  have hid : ‖(2 : ℂ) * r ^ 2 - 1‖ ^ 2 =
      4 * (‖r‖ ^ 2) ^ 2 + 4 * ‖r‖ ^ 2 + 1 - 2 * (2 * r.re) ^ 2 := by
    simp only [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
    <;> ring
  have hpos : 0 ≤ ‖r‖ ^ 2 + 2 * r.re := by linarith
  have hneg : 0 ≤ ‖r‖ ^ 2 - 2 * r.re := by linarith
  have htrace : (2 * r.re) ^ 2 ≤ (‖r‖ ^ 2) ^ 2 := by
    nlinarith only [mul_nonneg hpos hneg]
  nlinarith only [hid, htrace, hn, sq_nonneg (‖r‖ ^ 2 - 1)]





end D1Bound5
end
