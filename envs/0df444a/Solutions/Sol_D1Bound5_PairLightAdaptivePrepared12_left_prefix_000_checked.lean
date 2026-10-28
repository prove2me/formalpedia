-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:15:33.958265+00:00
-- url     : https://prove2.me/submissions/c6a9be21-ba68-4195-9677-d31ed5b4b1ca

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 137; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 138
      leftCached000 leftRows000 = true := by
  have h136 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 2
      (leftCached000.drop 136) (leftRows000.drop 136) = true := left_prefix_000_part04_checked
  have h095 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 43
      (leftCached000.drop 95) (leftRows000.drop 95) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared12.sieve 41 2
      (leftCached000.drop 95) (leftRows000.drop 95)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h136
  have h060 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 78
      (leftCached000.drop 60) (leftRows000.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared12.sieve 35 43
      (leftCached000.drop 60) (leftRows000.drop 60)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h095
  have h029 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 109
      (leftCached000.drop 29) (leftRows000.drop 29) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared12.sieve 31 78
      (leftCached000.drop 29) (leftRows000.drop 29)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h060
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 138
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared12.sieve 29 109
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h029
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared12
end
