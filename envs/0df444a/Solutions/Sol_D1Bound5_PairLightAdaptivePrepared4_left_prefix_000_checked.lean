-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:32.690641+00:00
-- url     : https://prove2.me/submissions/cecf0750-9c3e-4b15-92f7-22647d8a11f4

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 71
      leftCached000 leftRows000 = true := by
  have h0058 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 13
      (PairLightPrepared4.leftCached.drop 58) (PairLightPrepared4.leftRows.drop 58) = true := left_prefix_000_part05_checked
  have h0046 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 25
      (PairLightPrepared4.leftCached.drop 46) (PairLightPrepared4.leftRows.drop 46) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 12 13
      (PairLightPrepared4.leftCached.drop 46) (PairLightPrepared4.leftRows.drop 46)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0058
  have h0034 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 37
      (PairLightPrepared4.leftCached.drop 34) (PairLightPrepared4.leftRows.drop 34) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 12 25
      (PairLightPrepared4.leftCached.drop 34) (PairLightPrepared4.leftRows.drop 34)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0046
  have h0022 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 49
      (PairLightPrepared4.leftCached.drop 22) (PairLightPrepared4.leftRows.drop 22) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 12 37
      (PairLightPrepared4.leftCached.drop 22) (PairLightPrepared4.leftRows.drop 22)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0034
  have h0011 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 60
      (PairLightPrepared4.leftCached.drop 11) (PairLightPrepared4.leftRows.drop 11) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 11 49
      (PairLightPrepared4.leftCached.drop 11) (PairLightPrepared4.leftRows.drop 11)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0022
  have h0000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 71
      (PairLightPrepared4.leftCached.drop 0) (PairLightPrepared4.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 11 60
      (PairLightPrepared4.leftCached.drop 0) (PairLightPrepared4.leftRows.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0011
  simpa only [leftCached000, leftRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0000

end D1Bound5.PairLightAdaptivePrepared4
end
