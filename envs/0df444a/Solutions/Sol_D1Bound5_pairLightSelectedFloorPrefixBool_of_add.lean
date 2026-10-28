-- Prove2me | solution 1 for D1Bound5.pairLightSelectedFloorPrefixBool_of_add
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:55.627395+00:00
-- url     : https://prove2.me/submissions/7e0d0c3f-d909-4820-bd2a-90db7a6e3cb6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_add

section
namespace D1Bound5



/-- Join two checked finite prefixes without re-executing either certificate. -/
theorem _root_.solution
    (tau nu : Int) (sieve : List (Nat × Nat)) (m n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat))
    (hm : pairLightSelectedFloorPrefixBool tau nu sieve m cached rows = true)
    (hn : pairLightSelectedFloorPrefixBool tau nu sieve n
      (cached.drop m) (rows.drop m) = true) :
    pairLightSelectedFloorPrefixBool tau nu sieve (m+n) cached rows = true :=
  (pairLightSelectedFloorPrefixBool_add tau nu sieve m n cached rows).trans
    (Bool.and_eq_true_iff.mpr ⟨hm, hn⟩)

end D1Bound5
end
