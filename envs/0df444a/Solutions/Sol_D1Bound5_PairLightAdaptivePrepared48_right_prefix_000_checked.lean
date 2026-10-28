-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:22.102602+00:00
-- url     : https://prove2.me/submissions/e333aa6c-4efb-443c-911a-81d8c177e1cd

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 137; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 138
      rightCached000 rightRows000 = true := by
  have h137 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 1
      (rightCached000.drop 137) (rightRows000.drop 137) = true := right_prefix_000_part04_checked
  have h096 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 42
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 8 PairLightPrepared48.sieve 41 1
      (rightCached000.drop 96) (rightRows000.drop 96)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h137
  have h061 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 77
      (rightCached000.drop 61) (rightRows000.drop 61) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 8 PairLightPrepared48.sieve 35 42
      (rightCached000.drop 61) (rightRows000.drop 61)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h096
  have h029 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 109
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 8 PairLightPrepared48.sieve 32 77
      (rightCached000.drop 29) (rightRows000.drop 29)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h061
  have h000 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 138
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 8 PairLightPrepared48.sieve 29 109
      (rightCached000.drop 0) (rightRows000.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h029
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared48
end
