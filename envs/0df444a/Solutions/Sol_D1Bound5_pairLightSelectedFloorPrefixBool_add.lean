-- Prove2me | solution 1 for D1Bound5.pairLightSelectedFloorPrefixBool_add
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:18.472045+00:00
-- url     : https://prove2.me/submissions/471d34c8-afa3-4dba-87b3-92386031c07a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5

/-- Concatenate two finite head prefixes without shortening any head's tail.
The identity also covers malformed and unequal witness lists. -/
theorem _root_.solution
    (tau nu : Int) (sieve : List (Nat × Nat)) (m n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat)) :
    pairLightSelectedFloorPrefixBool tau nu sieve (m+n) cached rows =
      (pairLightSelectedFloorPrefixBool tau nu sieve m cached rows &&
        pairLightSelectedFloorPrefixBool tau nu sieve n (cached.drop m) (rows.drop m)) := by
  induction m generalizing cached rows with
  | zero =>
      simp only [Nat.zero_add, pairLightSelectedFloorPrefixBool, List.drop_zero, Bool.true_and]
  | succ m ih =>
      cases cached with
      | nil =>
          cases rows <;> cases n <;>
            simp [Nat.succ_add, pairLightSelectedFloorPrefixBool]
      | cons x xs =>
          cases rows with
          | nil => simp [Nat.succ_add, pairLightSelectedFloorPrefixBool]
          | cons item rows =>
              rcases item with ⟨code, ks⟩
              rw [Nat.succ_add]
              change
                (pairLightSelectedFloorRowBool tau nu sieve x xs code ks &&
                  pairLightSelectedFloorPrefixBool tau nu sieve (m+n) xs rows) =
                ((pairLightSelectedFloorRowBool tau nu sieve x xs code ks &&
                    pairLightSelectedFloorPrefixBool tau nu sieve m xs rows) &&
                  pairLightSelectedFloorPrefixBool tau nu sieve n (xs.drop m) (rows.drop m))
              rw [ih xs rows, Bool.and_assoc]



end D1Bound5
end
