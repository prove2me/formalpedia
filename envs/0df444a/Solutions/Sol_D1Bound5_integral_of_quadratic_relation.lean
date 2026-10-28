-- Prove2me | solution 1 for D1Bound5.integral_of_quadratic_relation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:01:11.787005+00:00
-- url     : https://prove2.me/submissions/df5e9686-1268-4f08-83fa-af1726c287b2

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module Polynomial

namespace D1Bound5

variable {K : Type*} [Field K]

/-- A field element satisfying an integral monic quadratic is integral. -/
theorem _root_.solution (a b : ℤ) {x : K}
    (h : x*x = (a : K)+(b : K)*x) : IsIntegral ℤ x := by
  refine ⟨X^2-(C b*X+C a), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le b) (by decide)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
    change x^2-((b : K)*x+(a : K)) = 0
    linear_combination h

variable [NumberField K]









end D1Bound5
end
