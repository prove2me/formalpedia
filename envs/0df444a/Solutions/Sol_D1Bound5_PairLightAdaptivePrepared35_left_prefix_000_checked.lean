-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:17:17.374124+00:00
-- url     : https://prove2.me/submissions/954343a7-d272-4a10-a53a-f3b4cea548f8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 131; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 132
      leftCached000 leftRows000 = true := by
  have h130 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 2
      (leftCached000.drop 130) (leftRows000.drop 130) = true := left_prefix_000_part04_checked
  have h092 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 40
      (leftCached000.drop 92) (leftRows000.drop 92) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 38 2
      (leftCached000.drop 92) (leftRows000.drop 92)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h130
  have h058 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 74
      (leftCached000.drop 58) (leftRows000.drop 58) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 34 40
      (leftCached000.drop 58) (leftRows000.drop 58)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h092
  have h028 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 104
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 30 74
      (leftCached000.drop 28) (leftRows000.drop 28)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h058
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 132
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 28 104
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h028
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared35
end
