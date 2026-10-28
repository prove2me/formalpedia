-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:30.208217+00:00
-- url     : https://prove2.me/submissions/4426ce13-cc41-434a-93b3-d8a8347bfb20

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 280; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 281
      rightCached000 rightRows000 = true := by
  have h140 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 141
      (rightCached000.drop 140) (rightRows000.drop 140) = true := right_prefix_000_part03_checked
  have h082 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 199
      (rightCached000.drop 82) (rightRows000.drop 82) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared38.sieve 58 141
      (rightCached000.drop 82) (rightRows000.drop 82)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h140
  have h038 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 243
      (rightCached000.drop 38) (rightRows000.drop 38) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared38.sieve 44 199
      (rightCached000.drop 38) (rightRows000.drop 38)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h082
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 281
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared38.sieve 38 243
      (rightCached000.drop 0) (rightRows000.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h038
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared38
end
