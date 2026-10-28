-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:32.948442+00:00
-- url     : https://prove2.me/submissions/7436974e-37f5-41e0-a3e5-446e79e0b9e1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 125 through 380; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 256
      rightCached001 rightRows001 = true := by
  have h148 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 108
      (rightCached001.drop 148) (rightRows001.drop 148) = true := right_prefix_001_part03_checked
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 172
      (rightCached001.drop 84) (rightRows001.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 64 108
      (rightCached001.drop 84) (rightRows001.drop 84)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h148
  have h038 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 218
      (rightCached001.drop 38) (rightRows001.drop 38) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 46 172
      (rightCached001.drop 38) (rightRows001.drop 38)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 256
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 38 218
      (rightCached001.drop 0) (rightRows001.drop 0)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h038
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared25
end
