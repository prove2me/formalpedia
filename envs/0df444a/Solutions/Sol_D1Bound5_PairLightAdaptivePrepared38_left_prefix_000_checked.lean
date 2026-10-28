-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:39.309928+00:00
-- url     : https://prove2.me/submissions/55614827-69ea-4dcf-881d-e4d9b8f96796

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 279; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 280
      leftCached000 leftRows000 = true := by
  have h140 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 140
      (leftCached000.drop 140) (leftRows000.drop 140) = true := left_prefix_000_part03_checked
  have h082 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 198
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared38.sieve 58 140
      (leftCached000.drop 82) (leftRows000.drop 82)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h140
  have h037 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 243
      (leftCached000.drop 37) (leftRows000.drop 37) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared38.sieve 45 198
      (leftCached000.drop 37) (leftRows000.drop 37)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h082
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 280
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared38.sieve 37 243
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h037
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared38
end
