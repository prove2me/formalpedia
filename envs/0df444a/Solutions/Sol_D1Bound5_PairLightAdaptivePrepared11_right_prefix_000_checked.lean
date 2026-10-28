-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:15.659832+00:00
-- url     : https://prove2.me/submissions/08e6b3f2-b5f3-45ec-bc69-0717d422d7e4

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 137; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 138
      rightCached000 rightRows000 = true := by
  have h108 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 30
      (rightCached000.drop 108) (rightRows000.drop 108) = true := right_prefix_000_part05_checked
  have h082 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 56
      (rightCached000.drop 82) (rightRows000.drop 82) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 26 30
      (rightCached000.drop 82) (rightRows000.drop 82)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h108
  have h058 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 80
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 24 56
      (rightCached000.drop 58) (rightRows000.drop 58)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h082
  have h036 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 102
      (rightCached000.drop 36) (rightRows000.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 22 80
      (rightCached000.drop 36) (rightRows000.drop 36)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h058
  have h016 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 122
      (rightCached000.drop 16) (rightRows000.drop 16) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 20 102
      (rightCached000.drop 16) (rightRows000.drop 16)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 138
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 16 122
      (rightCached000.drop 0) (rightRows000.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h016
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared11
end
