-- Prove2me | solution 1 for D1Bound5.quadInt_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:31.526211+00:00
-- url     : https://prove2.me/submissions/a3f2c80f-c194-4a0b-a66d-dea1db4852dc

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_eq_zero_iff

section
namespace D1Bound5
open QuadInt















/-- Positive-definite quadratic coordinates have no zero divisors. -/
theorem _root_.solution {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    {x y : QuadInt tau nu} (h : x*y = 0) : x = 0 ∨ y = 0 := by
  have hn : x.norm*y.norm = 0 := by
    have hn := congrArg (fun z : QuadInt tau nu => z.norm) h
    simpa using hn
  rcases mul_eq_zero.mp hn with hx | hy
  · exact Or.inl ((norm_eq_zero_iff hd x).1 hx)
  · exact Or.inr ((norm_eq_zero_iff hd y).1 hy)



















end D1Bound5
end
