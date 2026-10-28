-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:52:51.047699+00:00
-- url     : https://prove2.me/submissions/85524742-307f-42ee-ad30-46cbf03c7013

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 136; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 137
      leftCached000 leftRows000 = true := by
  have h108 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 29
      (leftCached000.drop 108) (leftRows000.drop 108) = true := left_prefix_000_part05_checked
  have h082 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 55
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 26 29
      (leftCached000.drop 82) (leftRows000.drop 82)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h108
  have h058 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 79
      (leftCached000.drop 58) (leftRows000.drop 58) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 24 55
      (leftCached000.drop 58) (leftRows000.drop 58)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h082
  have h036 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 101
      (leftCached000.drop 36) (leftRows000.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 22 79
      (leftCached000.drop 36) (leftRows000.drop 36)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h058
  have h016 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 121
      (leftCached000.drop 16) (leftRows000.drop 16) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 20 101
      (leftCached000.drop 16) (leftRows000.drop 16)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 137
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared1.sieve 16 121
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h016
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared1
end
