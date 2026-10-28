-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:31:59.360268+00:00
-- url     : https://prove2.me/submissions/a6c072c0-d4a9-4224-9d86-d9d2902f0f99

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 136; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 137
      leftCached000 leftRows000 = true := by
  have h134 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := left_prefix_000_part04_checked
  have h094 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 43
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared17.sieve 40 3
      (leftCached000.drop 94) (leftRows000.drop 94)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h134
  have h059 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 78
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared17.sieve 35 43
      (leftCached000.drop 59) (leftRows000.drop 59)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h094
  have h028 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 109
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared17.sieve 31 78
      (leftCached000.drop 28) (leftRows000.drop 28)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h059
  have h000 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 137
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared17.sieve 28 109
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h028
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared17
end
