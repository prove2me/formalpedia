-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:28:31.644023+00:00
-- url     : https://prove2.me/submissions/3e70de4a-4999-4405-95ba-74651a8fcc4a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 71
      rightCached001 rightRows001 = true := by
  have h0123 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.rightCached.drop 123) (PairLightPrepared6.rightRows.drop 123) = true := right_prefix_001_part05_checked
  have h0111 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 24
      (PairLightPrepared6.rightCached.drop 111) (PairLightPrepared6.rightRows.drop 111) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 12
      (PairLightPrepared6.rightCached.drop 111) (PairLightPrepared6.rightRows.drop 111)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0123
  have h0099 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 36
      (PairLightPrepared6.rightCached.drop 99) (PairLightPrepared6.rightRows.drop 99) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 24
      (PairLightPrepared6.rightCached.drop 99) (PairLightPrepared6.rightRows.drop 99)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0111
  have h0087 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 48
      (PairLightPrepared6.rightCached.drop 87) (PairLightPrepared6.rightRows.drop 87) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 36
      (PairLightPrepared6.rightCached.drop 87) (PairLightPrepared6.rightRows.drop 87)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0099
  have h0075 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 60
      (PairLightPrepared6.rightCached.drop 75) (PairLightPrepared6.rightRows.drop 75) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 48
      (PairLightPrepared6.rightCached.drop 75) (PairLightPrepared6.rightRows.drop 75)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0087
  have h0064 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 71
      (PairLightPrepared6.rightCached.drop 64) (PairLightPrepared6.rightRows.drop 64) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 60
      (PairLightPrepared6.rightCached.drop 64) (PairLightPrepared6.rightRows.drop 64)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0075
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0064

end D1Bound5.PairLightAdaptivePrepared6
end
