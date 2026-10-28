-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:19.346004+00:00
-- url     : https://prove2.me/submissions/c3246cb5-de8d-4d99-b427-8c0ad02ff88a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 71
      rightCached000 rightRows000 = true := by
  have h0058 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.rightCached.drop 58) (PairLightPrepared10.rightRows.drop 58) = true := right_prefix_000_part05_checked
  have h0046 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 25
      (PairLightPrepared10.rightCached.drop 46) (PairLightPrepared10.rightRows.drop 46) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 12 13
      (PairLightPrepared10.rightCached.drop 46) (PairLightPrepared10.rightRows.drop 46)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0058
  have h0034 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 37
      (PairLightPrepared10.rightCached.drop 34) (PairLightPrepared10.rightRows.drop 34) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 12 25
      (PairLightPrepared10.rightCached.drop 34) (PairLightPrepared10.rightRows.drop 34)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0046
  have h0022 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 49
      (PairLightPrepared10.rightCached.drop 22) (PairLightPrepared10.rightRows.drop 22) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 12 37
      (PairLightPrepared10.rightCached.drop 22) (PairLightPrepared10.rightRows.drop 22)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0034
  have h0011 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 60
      (PairLightPrepared10.rightCached.drop 11) (PairLightPrepared10.rightRows.drop 11) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 11 49
      (PairLightPrepared10.rightCached.drop 11) (PairLightPrepared10.rightRows.drop 11)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0022
  have h0000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 71
      (PairLightPrepared10.rightCached.drop 0) (PairLightPrepared10.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 11 60
      (PairLightPrepared10.rightCached.drop 0) (PairLightPrepared10.rightRows.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0011
  simpa only [rightCached000, rightRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0000

end D1Bound5.PairLightAdaptivePrepared10
end
