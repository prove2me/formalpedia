-- Prove2me | solution 1 for D1Bound5.mutate_eq_supplied_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:18.744642+00:00
-- url     : https://prove2.me/submissions/c8efbc12-470c-4714-8fdd-fd44f075cd55

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
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Theorems.Thm_D1Bound5_quadInt_root_eq_or_neg_of_sq_eq

section
namespace D1Bound5
open QuadInt











/-- Arbitrary genuine root choices give one of the two supplied-root
mutations, including when one of the roots is zero. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b z r0 r s R0 R S : QuadInt tau nu)
    (h0 : r0 * r0 = a * b + 1) (hr : r * r = a * z + 1)
    (hs : s * s = b * z + 1) (hR0 : R0 * R0 = a * b + 1)
    (hR : R * R = a * z + 1) (hS : S * S = b * z + 1) :
    mutate a b z R0 R S = mutate a b z r0 r s ∨
      mutate a b z R0 R S = mutate a b z r0 r (-s) := by
  rcases quadInt_root_eq_or_neg_of_sq_eq hd R0 r0 (hR0.trans h0.symm) with h0 | h0 <;>
    rcases quadInt_root_eq_or_neg_of_sq_eq hd R r (hR.trans hr.symm) with hr | hr <;>
    rcases quadInt_root_eq_or_neg_of_sq_eq hd S s (hS.trans hs.symm) with hs | hs
  all_goals rw [h0, hr, hs]
  all_goals unfold mutate
  · left; ring
  · right; ring
  · right; ring
  · left; ring
  · right; ring
  · left; ring
  · left; ring
  · right; ring









end D1Bound5
end
