-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:27.554393+00:00
-- url     : https://prove2.me/submissions/bcf1760c-e156-4eda-a8a5-2a9991da0723

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 64
      rightCached000 rightRows000 = true := by
  have h0053 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.rightCached.drop 53) (PairLightPrepared6.rightRows.drop 53) = true := right_prefix_000_part05_checked
  have h0042 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 22
      (PairLightPrepared6.rightCached.drop 42) (PairLightPrepared6.rightRows.drop 42) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 11
      (PairLightPrepared6.rightCached.drop 42) (PairLightPrepared6.rightRows.drop 42)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0053
  have h0031 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 33
      (PairLightPrepared6.rightCached.drop 31) (PairLightPrepared6.rightRows.drop 31) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 22
      (PairLightPrepared6.rightCached.drop 31) (PairLightPrepared6.rightRows.drop 31)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0042
  have h0020 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 44
      (PairLightPrepared6.rightCached.drop 20) (PairLightPrepared6.rightRows.drop 20) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 33
      (PairLightPrepared6.rightCached.drop 20) (PairLightPrepared6.rightRows.drop 20)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0031
  have h0010 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 54
      (PairLightPrepared6.rightCached.drop 10) (PairLightPrepared6.rightRows.drop 10) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 10 44
      (PairLightPrepared6.rightCached.drop 10) (PairLightPrepared6.rightRows.drop 10)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0020
  have h0000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 64
      (PairLightPrepared6.rightCached.drop 0) (PairLightPrepared6.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 10 54
      (PairLightPrepared6.rightCached.drop 0) (PairLightPrepared6.rightRows.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0010
  simpa only [rightCached000, rightRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0000

end D1Bound5.PairLightAdaptivePrepared6
end
