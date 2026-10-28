-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:15:32.226256+00:00
-- url     : https://prove2.me/submissions/2a3c2214-a3a5-4165-b86b-6b75c075bbb9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 138 through 358; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 221
      rightCached001 rightRows001 = true := by
  have h132 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 89
      (rightCached001.drop 132) (rightRows001.drop 132) = true := right_prefix_001_part03_checked
  have h076 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 145
      (rightCached001.drop 76) (rightRows001.drop 76) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 56 89
      (rightCached001.drop 76) (rightRows001.drop 76)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h132
  have h034 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 187
      (rightCached001.drop 34) (rightRows001.drop 34) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 42 145
      (rightCached001.drop 34) (rightRows001.drop 34)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h076
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 221
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared11.sieve 34 187
      (rightCached001.drop 0) (rightRows001.drop 0)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h034
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared11
end
