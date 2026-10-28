-- Prove2me | solution 1 for D1Bound5.pairGraphTriangleFreeBool_of_no_three_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:54.538751+00:00
-- url     : https://prove2.me/submissions/8f326dc5-ffc3-4996-8f07-9240d3672c5d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Theorems.Thm_D1Bound5_hasSquareRootFast_iff

section
namespace D1Bound5
open QuadInt

/-- A mathematical exclusion of three nonzero compatible points supplies
exactly the original triangle Boolean, without enumerating the pairs. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (vertices : List (QuadInt tau nu))
    (hno : ∀ x y z : QuadInt tau nu,
      x ∈ vertices → y ∈ vertices → z ∈ vertices →
      x ≠ 0 → y ≠ 0 → z ≠ 0 →
      (∃ r, r*r = x*y+1) → (∃ r, r*r = x*z+1) →
      (∃ r, r*r = y*z+1) → False) :
    pairGraphTriangleFreeBool sieve vertices = true := by
  unfold pairGraphTriangleFreeBool
  apply List.all_eq_true.mpr
  intro a ha
  by_cases hga : decide (a ≠ 0) = true
  · rw [if_pos hga]
    have ha0 : a ≠ 0 := of_decide_eq_true hga
    apply List.all_eq_true.mpr
    intro b hb
    by_cases hgb : decide (b ≠ 0 ∧ a ≠ b) = true
    · rw [if_pos hgb]
      have hgb' : b ≠ 0 ∧ a ≠ b := of_decide_eq_true hgb
      by_cases hsab : hasSquareRootFast sieve (a*b+1) = true
      · rw [if_pos hsab]
        apply List.all_eq_true.mpr
        intro c hc
        by_cases hgc : decide (c ≠ 0 ∧ a ≠ c ∧ b ≠ c) = true
        · rw [if_pos hgc]
          have hgc' : c ≠ 0 ∧ a ≠ c ∧ b ≠ c := of_decide_eq_true hgc
          cases hsac : hasSquareRootFast sieve (a*c+1) <;>
            cases hsbc : hasSquareRootFast sieve (b*c+1) <;> try rfl
          exact (hno a b c ha hb hc ha0 hgb'.1 hgc'.1
            ((hasSquareRootFast_iff hd sieve hvalid _).1 hsab)
            ((hasSquareRootFast_iff hd sieve hvalid _).1 hsac)
            ((hasSquareRootFast_iff hd sieve hvalid _).1 hsbc)).elim
        · rw [if_neg hgc]
      · rw [if_neg hsab]
    · rw [if_neg hgb]
  · rw [if_neg hga]





end D1Bound5
end
