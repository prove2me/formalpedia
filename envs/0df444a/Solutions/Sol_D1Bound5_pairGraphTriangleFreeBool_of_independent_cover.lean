-- Prove2me | solution 1 for D1Bound5.pairGraphTriangleFreeBool_of_independent_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:35:31.982797+00:00
-- url     : https://prove2.me/submissions/e28fe7f4-0cc5-4163-874d-00efa00f3014

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
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Theorems.Thm_D1Bound5_pairIndependentBool_sound

section
namespace D1Bound5
open QuadInt









/-- A certified two-color overgraph supplies the original triangle Boolean.
Only within-color nonedges are checked; cross-color pairs remain arbitrary. -/
theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices left right : List (QuadInt tau nu))
    (hcover : ∀ z ∈ vertices, z ∈ left ∨ z ∈ right)
    (hleft : pairIndependentBool sieve left = true)
    (hright : pairIndependentBool sieve right = true) :
    pairGraphTriangleFreeBool sieve vertices = true := by
  have no_triangle (a b c : QuadInt tau nu)
      (ha : a ∈ vertices) (hb : b ∈ vertices) (hc : c ∈ vertices)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hsab : hasSquareRootFast sieve (a*b+1) = true)
      (hsac : hasSquareRootFast sieve (a*c+1) = true)
      (hsbc : hasSquareRootFast sieve (b*c+1) = true) : False := by
    have reject_left (x y : QuadInt tau nu) (hx : x ∈ left) (hy : y ∈ left)
        (hxy : x ≠ y) (hs : hasSquareRootFast sieve (x*y+1) = true) : False := by
      have hf := pairIndependentBool_sound sieve left hleft x y hx hy hxy
      simp only [hf, Bool.false_eq_true] at hs
    have reject_right (x y : QuadInt tau nu) (hx : x ∈ right) (hy : y ∈ right)
        (hxy : x ≠ y) (hs : hasSquareRootFast sieve (x*y+1) = true) : False := by
      have hf := pairIndependentBool_sound sieve right hright x y hx hy hxy
      simp only [hf, Bool.false_eq_true] at hs
    rcases hcover a ha with hal | har
    · rcases hcover b hb with hbl | hbr
      · exact reject_left a b hal hbl hab hsab
      · rcases hcover c hc with hcl | hcr
        · exact reject_left a c hal hcl hac hsac
        · exact reject_right b c hbr hcr hbc hsbc
    · rcases hcover b hb with hbl | hbr
      · rcases hcover c hc with hcl | hcr
        · exact reject_left b c hbl hcl hbc hsbc
        · exact reject_right a c har hcr hac hsac
      · exact reject_right a b har hbr hab hsab
  unfold pairGraphTriangleFreeBool
  apply List.all_eq_true.mpr
  intro a ha
  by_cases hga : decide (a ≠ 0) = true
  · rw [if_pos hga]
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
          exact (no_triangle a b c ha hb hc hgb'.2 hgc'.2.1 hgc'.2.2
            hsab hsac hsbc).elim
        · rw [if_neg hgc]
      · rw [if_neg hsab]
    · rw [if_neg hgb]
  · rw [if_neg hga]



end D1Bound5
end
