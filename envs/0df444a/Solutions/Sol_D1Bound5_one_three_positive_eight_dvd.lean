-- Prove2me | solution 1 for D1Bound5.one_three_positive_eight_dvd
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:59.476131+00:00
-- url     : https://prove2.me/submissions/57aac357-ff0a-4240-a910-2446725f4b18

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5













/-- Positive rational common extensions of 1 and 3 are multiples of eight. -/
theorem _root_.solution {p r s : ℤ}
    (hr : p+1=r^2) (hs : 3*p+1=s^2) : 8 ∣ p := by
  have hr0 : 0 ≤ r % 8 := Int.emod_nonneg r (by norm_num)
  have hr8 : r % 8 < 8 := Int.emod_lt_of_pos r (by norm_num)
  have hs0 : 0 ≤ s % 8 := Int.emod_nonneg s (by norm_num)
  have hs8 : s % 8 < 8 := Int.emod_lt_of_pos s (by norm_num)
  have her : r^2 % 8 = ((r % 8)*(r % 8)) % 8 := by rw [pow_two, Int.mul_emod]
  have hes : s^2 % 8 = ((s % 8)*(s % 8)) % 8 := by rw [pow_two, Int.mul_emod]
  apply Int.dvd_of_emod_eq_zero
  interval_cases hri : r % 8 <;> interval_cases hsi : s % 8 <;>
    norm_num [hri,hsi] at her hes <;> omega

















end D1Bound5
end
