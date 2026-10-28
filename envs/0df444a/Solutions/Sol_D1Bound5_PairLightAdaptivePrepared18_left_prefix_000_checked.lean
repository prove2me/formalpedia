-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:27:30.05031+00:00
-- url     : https://prove2.me/submissions/972d4bfa-f10a-4a0d-9993-ff43e5d54623

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 261; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 262
      leftCached000 leftRows000 = true := by
  have h131 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 131
      (leftCached000.drop 131) (leftRows000.drop 131) = true := left_prefix_000_part03_checked
  have h077 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 185
      (leftCached000.drop 77) (leftRows000.drop 77) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared18.sieve 54 131
      (leftCached000.drop 77) (leftRows000.drop 77)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h131
  have h035 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 227
      (leftCached000.drop 35) (leftRows000.drop 35) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared18.sieve 42 185
      (leftCached000.drop 35) (leftRows000.drop 35)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h077
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 262
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared18.sieve 35 227
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h035
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared18
end
