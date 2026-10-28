-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:17.49976+00:00
-- url     : https://prove2.me/submissions/3661ea19-fac0-4bc8-9a4f-00a545818592

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 126
      leftCached000 leftRows000 = true := by
  have h109 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 17
      (leftCached000.drop 109) (leftRows000.drop 109) = true := left_prefix_000_part04_checked
  have h078 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 48
      (leftCached000.drop 78) (leftRows000.drop 78) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 31 17
      (leftCached000.drop 78) (leftRows000.drop 78)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h109
  have h050 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 76
      (leftCached000.drop 50) (leftRows000.drop 50) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 28 48
      (leftCached000.drop 50) (leftRows000.drop 50)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h078
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 102
      (leftCached000.drop 24) (leftRows000.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 26 76
      (leftCached000.drop 24) (leftRows000.drop 24)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h050
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 126
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 24 102
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared29
end
