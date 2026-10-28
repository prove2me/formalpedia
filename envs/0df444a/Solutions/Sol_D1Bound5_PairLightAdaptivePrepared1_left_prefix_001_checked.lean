-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:43.87518+00:00
-- url     : https://prove2.me/submissions/85958f81-ddfe-4bac-98f1-45926acdacb2

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 137 through 359; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 223
      leftCached001 leftRows001 = true := by
  have h132 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 91
      (leftCached001.drop 132) (leftRows001.drop 132) = true := left_prefix_001_part03_checked
  have h076 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 147
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 56 91
      (leftCached001.drop 76) (leftRows001.drop 76)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h132
  have h034 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 189
      (leftCached001.drop 34) (leftRows001.drop 34) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 42 147
      (leftCached001.drop 34) (leftRows001.drop 34)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h076
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 223
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 34 189
      (leftCached001.drop 0) (leftRows001.drop 0)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h034
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared1
end
