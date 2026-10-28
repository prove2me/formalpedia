-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:17.627892+00:00
-- url     : https://prove2.me/submissions/3d7685c9-b556-4004-ad95-c066f5d0374c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 136; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 137
      leftCached000 leftRows000 = true := by
  have h134 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := left_prefix_000_part04_checked
  have h094 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 43
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared33.sieve 40 3
      (leftCached000.drop 94) (leftRows000.drop 94)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h134
  have h059 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 78
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared33.sieve 35 43
      (leftCached000.drop 59) (leftRows000.drop 59)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h094
  have h028 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 109
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared33.sieve 31 78
      (leftCached000.drop 28) (leftRows000.drop 28)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h059
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 137
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared33.sieve 28 109
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h028
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared33
end
