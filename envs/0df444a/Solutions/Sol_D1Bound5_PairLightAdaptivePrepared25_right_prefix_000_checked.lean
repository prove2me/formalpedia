-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:08.242627+00:00
-- url     : https://prove2.me/submissions/86e5bc01-9585-49fe-bc4b-250535ef9a40

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 124; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 125
      rightCached000 rightRows000 = true := by
  have h109 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 16
      (rightCached000.drop 109) (rightRows000.drop 109) = true := right_prefix_000_part04_checked
  have h078 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 47
      (rightCached000.drop 78) (rightRows000.drop 78) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 31 16
      (rightCached000.drop 78) (rightRows000.drop 78)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h109
  have h050 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 75
      (rightCached000.drop 50) (rightRows000.drop 50) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 28 47
      (rightCached000.drop 50) (rightRows000.drop 50)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h078
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 101
      (rightCached000.drop 24) (rightRows000.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 26 75
      (rightCached000.drop 24) (rightRows000.drop 24)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h050
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 125
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared25.sieve 24 101
      (rightCached000.drop 0) (rightRows000.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared25
end
