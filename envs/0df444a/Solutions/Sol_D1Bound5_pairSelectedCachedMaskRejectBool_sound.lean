-- Prove2me | solution 1 for D1Bound5.pairSelectedCachedMaskRejectBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:50.818276+00:00
-- url     : https://prove2.me/submissions/3fa9753b-d019-408e-869a-8fc45cd4620b

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions

section
namespace D1Bound5



/-- One genuinely rejecting aligned conjunct makes the entire original
cached sieve false. This is a statement about the exact old Boolean, so no
signature-validity, mask-validity, or discriminant assumption is needed. -/
theorem _root_.solution (tau nu : ℤ)
    (sieve : List (ℕ × ℕ)) (xs ys : List (ℕ × ℕ)) (i : ℕ)
    (hcheck : pairSelectedCachedMaskRejectBool tau nu sieve xs ys i = true) :
    pairCachedCoordinateSieveBool tau nu sieve xs ys = false := by
  induction i generalizing sieve xs ys with
  | zero =>
      cases sieve with
      | nil => simp [pairSelectedCachedMaskRejectBool] at hcheck
      | cons item sieve =>
          cases xs with
          | nil => rfl
          | cons u xs =>
              cases ys with
              | nil => rfl
              | cons v ys =>
                  rcases item with ⟨k, mask⟩
                  change (!pairResidueMaskBool tau nu k mask u v) = true at hcheck
                  change (pairResidueMaskBool tau nu k mask u v &&
                    pairCachedCoordinateSieveBool tau nu sieve xs ys) = false
                  cases hm : pairResidueMaskBool tau nu k mask u v with
                  | false => simp only [Bool.false_and]
                  | true =>
                      simp only [hm, Bool.not_true, Bool.false_eq_true] at hcheck
  | succ i ih =>
      cases sieve with
      | nil => simp [pairSelectedCachedMaskRejectBool] at hcheck
      | cons item sieve =>
          cases xs with
          | nil => rfl
          | cons u xs =>
              cases ys with
              | nil => rfl
              | cons v ys =>
                  change pairSelectedCachedMaskRejectBool tau nu sieve xs ys i = true at hcheck
                  have htail := ih sieve xs ys hcheck
                  rcases item with ⟨k, mask⟩
                  change (pairResidueMaskBool tau nu k mask u v &&
                    pairCachedCoordinateSieveBool tau nu sieve xs ys) = false
                  rw [htail, Bool.and_false]

end D1Bound5
end
