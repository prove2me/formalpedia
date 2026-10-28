-- Prove2me | solution 1 for D1Bound5.quadInt_root_eq_or_neg_of_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:19.575511+00:00
-- url     : https://prove2.me/submissions/cd902582-14d1-48bc-8bbb-6124e3e5c164

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
import Theorems.Thm_D1Bound5_quadInt_mul_eq_zero

section
namespace D1Bound5
open QuadInt









/-- In positive-definite quadratic coordinates, two square roots of the same
element agree up to sign. Neither root is required to be canonical. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (r q : QuadInt tau nu)
    (h : r * r = q * q) : r = q ∨ r = -q := by
  have hf : (r - q) * (r + q) = 0 := by
    calc
      _ = r * r - q * q := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases quadInt_mul_eq_zero hd hf with hzero | hzero
  · exact Or.inl (sub_eq_zero.mp hzero)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hzero)











end D1Bound5
end
