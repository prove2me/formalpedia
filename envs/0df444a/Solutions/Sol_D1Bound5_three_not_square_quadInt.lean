-- Prove2me | solution 1 for D1Bound5.three_not_square_quadInt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:20.508005+00:00
-- url     : https://prove2.me/submissions/d10719d2-cce7-4d5d-a89e-225c91aabcea

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_positive_integer_square_is_integer

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



/-- The rational integer three is not a square in any positive-discriminant
quadratic integer coordinate ring, including all half-integral models. -/
theorem _root_.solution {tau nu : ℤ}
    (hpos : 0 < discriminant tau nu) :
    ¬ ∃ r : QuadInt tau nu, r*r = 3 := by
  intro hr
  obtain ⟨n, hn⟩ := positive_integer_square_is_integer hpos (by norm_num : (0:ℤ)<3) hr
  have hlo : -2 ≤ n := by nlinarith [sq_nonneg (n+2)]
  have hhi : n ≤ 2 := by nlinarith [sq_nonneg (n-2)]
  interval_cases n <;> norm_num at hn









end D1Bound5
end
