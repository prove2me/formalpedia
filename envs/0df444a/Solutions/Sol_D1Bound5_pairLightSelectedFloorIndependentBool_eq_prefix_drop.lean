-- Prove2me | solution 1 for D1Bound5.pairLightSelectedFloorIndependentBool_eq_prefix_drop
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:39.122334+00:00
-- url     : https://prove2.me/submissions/625b1789-3bf5-486b-a37e-a113b9545c43

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5

/-- Exact factorization for all inputs, including malformed witness lists.
The first factor checks each early head against its full tail. -/
theorem _root_.solution
    (tau nu : Int) (sieve : List (Nat × Nat)) (n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat)) :
    pairLightSelectedFloorIndependentBool tau nu sieve cached rows =
      (pairLightSelectedFloorPrefixBool tau nu sieve n cached rows &&
        pairLightSelectedFloorIndependentBool tau nu sieve (cached.drop n) (rows.drop n)) := by
  induction n generalizing cached rows with
  | zero =>
      simp only [pairLightSelectedFloorPrefixBool, List.drop_zero, Bool.true_and]
  | succ n ih =>
      cases cached with
      | nil => cases rows <;> rfl
      | cons x xs =>
          cases rows with
          | nil => rfl
          | cons item rows =>
              rcases item with ⟨code, ks⟩
              change
                (pairLightSelectedFloorRowBool tau nu sieve x xs code ks &&
                  pairLightSelectedFloorIndependentBool tau nu sieve xs rows) =
                ((pairLightSelectedFloorRowBool tau nu sieve x xs code ks &&
                    pairLightSelectedFloorPrefixBool tau nu sieve n xs rows) &&
                  pairLightSelectedFloorIndependentBool tau nu sieve (xs.drop n) (rows.drop n))
              rw [ih xs rows, Bool.and_assoc]





end D1Bound5
end
