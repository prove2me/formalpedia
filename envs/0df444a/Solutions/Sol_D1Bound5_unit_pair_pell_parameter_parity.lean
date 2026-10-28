-- Prove2me | solution 1 for D1Bound5.unit_pair_pell_parameter_parity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:02.747368+00:00
-- url     : https://prove2.me/submissions/1c935682-1606-4ae5-8d43-ac05c8e2ef80

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5

private theorem integer_square_mod_eight (u : ℤ) :
    u ^ 2 % 8 = 0 ∨ u ^ 2 % 8 = 1 ∨ u ^ 2 % 8 = 4 := by
  have h0 : 0 ≤ u % 8 := Int.emod_nonneg _ (by decide)
  have h8 : u % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  interval_cases hu : u % 8 <;> norm_num [pow_two, Int.mul_emod, hu]

/-- A norm-two Pell solution has one of precisely the two relevant
parameter congruences. No primitivity or positive-root assumption is used. -/
theorem _root_.solution (d u v : ℤ)
    (h : u ^ 2 - d * v ^ 2 = 2) : d % 8 = 7 ∨ d % 4 = 2 := by
  have hm := congrArg (fun x : ℤ => x % 8) h
  have hd0 : 0 ≤ d % 8 := Int.emod_nonneg _ (by decide)
  have hd8 : d % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  rcases integer_square_mod_eight u with hu | hu | hu <;>
    rcases integer_square_mod_eight v with hv | hv | hv <;>
    interval_cases hd : d % 8 <;>
    norm_num [Int.sub_emod, Int.mul_emod, hu, hv, hd] at hm <;> omega







end D1Bound5
end
