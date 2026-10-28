-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:23.461235+00:00
-- url     : https://prove2.me/submissions/94507142-f453-4b08-bf6f-09f774af601e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 58
      leftCached000 leftRows000 = true := by
  have h0048 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.leftCached.drop 48) (PairLightPrepared8.leftRows.drop 48) = true := left_prefix_000_part05_checked
  have h0038 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 20
      (PairLightPrepared8.leftCached.drop 38) (PairLightPrepared8.leftRows.drop 38) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 10 10
      (PairLightPrepared8.leftCached.drop 38) (PairLightPrepared8.leftRows.drop 38)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0048
  have h0028 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 30
      (PairLightPrepared8.leftCached.drop 28) (PairLightPrepared8.leftRows.drop 28) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 10 20
      (PairLightPrepared8.leftCached.drop 28) (PairLightPrepared8.leftRows.drop 28)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0038
  have h0018 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 40
      (PairLightPrepared8.leftCached.drop 18) (PairLightPrepared8.leftRows.drop 18) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 10 30
      (PairLightPrepared8.leftCached.drop 18) (PairLightPrepared8.leftRows.drop 18)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0028
  have h0009 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 49
      (PairLightPrepared8.leftCached.drop 9) (PairLightPrepared8.leftRows.drop 9) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 9 40
      (PairLightPrepared8.leftCached.drop 9) (PairLightPrepared8.leftRows.drop 9)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0018
  have h0000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 58
      (PairLightPrepared8.leftCached.drop 0) (PairLightPrepared8.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 9 49
      (PairLightPrepared8.leftCached.drop 0) (PairLightPrepared8.leftRows.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0009
  simpa only [leftCached000, leftRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0000

end D1Bound5.PairLightAdaptivePrepared8
end
