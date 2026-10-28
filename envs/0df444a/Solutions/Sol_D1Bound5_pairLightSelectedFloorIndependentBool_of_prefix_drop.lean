-- Prove2me | solution 1 for D1Bound5.pairLightSelectedFloorIndependentBool_of_prefix_drop
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:21.661495+00:00
-- url     : https://prove2.me/submissions/9e92b380-2699-42cc-a320-1aaf58130f12

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_eq_prefix_drop

section
namespace D1Bound5



/-- Assemble already checked proof constants without rerunning their arithmetic. -/
theorem _root_.solution
    (tau nu : Int) (sieve : List (Nat × Nat)) (n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat))
    (hprefix : pairLightSelectedFloorPrefixBool tau nu sieve n cached rows = true)
    (htail : pairLightSelectedFloorIndependentBool tau nu sieve
      (cached.drop n) (rows.drop n) = true) :
    pairLightSelectedFloorIndependentBool tau nu sieve cached rows = true :=
  (pairLightSelectedFloorIndependentBool_eq_prefix_drop tau nu sieve n cached rows).trans
    (Bool.and_eq_true_iff.mpr ⟨hprefix, htail⟩)



end D1Bound5
end
