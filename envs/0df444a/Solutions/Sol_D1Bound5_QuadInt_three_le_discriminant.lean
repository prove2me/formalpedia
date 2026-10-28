-- Prove2me | solution 1 for D1Bound5.QuadInt.three_le_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:26.36229+00:00
-- url     : https://prove2.me/submissions/b77cc837-5c12-44b1-9f76-96a79a66f6d2

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5

/-- Every positive discriminant of an integral quadratic coordinate ring is
at least three, including nonmaximal orders. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) :
    3 ≤ QuadInt.discriminant tau nu := by
  have hm : tau^2 % 4 = ((tau % 4)*(tau % 4)) % 4 := by
    rw [pow_two, Int.mul_emod]
  have ht : tau % 4 = 0 ∨ tau % 4 = 1 ∨ tau % 4 = 2 ∨ tau % 4 = 3 := by omega
  have hs : tau^2 % 4 = 0 ∨ tau^2 % 4 = 1 := by
    rcases ht with ht | ht | ht | ht <;> norm_num [hm, ht]
  unfold QuadInt.discriminant at hd ⊢
  rcases hs with hs | hs <;> omega








end D1Bound5
end
