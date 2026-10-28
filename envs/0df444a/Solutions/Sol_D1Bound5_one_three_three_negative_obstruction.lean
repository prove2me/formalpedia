-- Prove2me | solution 1 for D1Bound5.one_three_three_negative_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:34.151709+00:00
-- url     : https://prove2.me/submissions/ca66339a-6e65-4343-a352-e097a8b8b23e

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









private theorem int_square_mod_four (z : ℤ) : z^2 % 4 = 0 ∨ z^2 % 4 = 1 := by
  have hr : 0 ≤ z % 4 := Int.emod_nonneg z (by norm_num)
  have hu : z % 4 < 4 := Int.emod_lt_of_pos z (by norm_num)
  have he : z^2 % 4 = ((z % 4)*(z % 4)) % 4 := by rw [pow_two, Int.mul_emod]
  interval_cases h : z % 4 <;> norm_num [h] at he ⊢ <;> omega







/-- Three odd negative extensions cannot be pairwise compatible. -/
theorem _root_.solution (x y z r s t : ℤ)
    (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1)
    (hr : x*y+1=r^2) (hs : x*z+1=s^2) (ht : y*z+1=t^2) : False := by
  have hxr : x % 4 = 1 ∨ x % 4 = 3 := by omega
  have hyr : y % 4 = 1 ∨ y % 4 = 3 := by omega
  have hzr : z % 4 = 1 ∨ z % 4 = 3 := by omega
  have her : (x*y+1)%4 = ((x%4)*(y%4)+1)%4 := by simp [Int.add_emod, Int.mul_emod]
  have hes : (x*z+1)%4 = ((x%4)*(z%4)+1)%4 := by simp [Int.add_emod, Int.mul_emod]
  have het : (y*z+1)%4 = ((y%4)*(z%4)+1)%4 := by simp [Int.add_emod, Int.mul_emod]
  have hrr := int_square_mod_four r
  have hss := int_square_mod_four s
  have htt := int_square_mod_four t
  rcases hxr with hx | hx <;> rcases hyr with hy | hy <;> rcases hzr with hz | hz <;>
    norm_num [hx,hy,hz,hr,hs,ht] at her hes het <;> omega













end D1Bound5
end
