-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:28:30.594975+00:00
-- url     : https://prove2.me/submissions/a50fa61f-d432-457b-b48f-3bf062ebf1f0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 82
      leftCached002 leftRows002 = true := by
  have h0202 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 14
      (PairLightPrepared6.leftCached.drop 202) (PairLightPrepared6.leftRows.drop 202) = true := left_prefix_002_part05_checked
  have h0188 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 28
      (PairLightPrepared6.leftCached.drop 188) (PairLightPrepared6.leftRows.drop 188) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 14 14
      (PairLightPrepared6.leftCached.drop 188) (PairLightPrepared6.leftRows.drop 188)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0202
  have h0174 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 42
      (PairLightPrepared6.leftCached.drop 174) (PairLightPrepared6.leftRows.drop 174) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 14 28
      (PairLightPrepared6.leftCached.drop 174) (PairLightPrepared6.leftRows.drop 174)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0188
  have h0160 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 56
      (PairLightPrepared6.leftCached.drop 160) (PairLightPrepared6.leftRows.drop 160) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 14 42
      (PairLightPrepared6.leftCached.drop 160) (PairLightPrepared6.leftRows.drop 160)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0174
  have h0147 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 69
      (PairLightPrepared6.leftCached.drop 147) (PairLightPrepared6.leftRows.drop 147) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 13 56
      (PairLightPrepared6.leftCached.drop 147) (PairLightPrepared6.leftRows.drop 147)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0160
  have h0134 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 82
      (PairLightPrepared6.leftCached.drop 134) (PairLightPrepared6.leftRows.drop 134) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 13 69
      (PairLightPrepared6.leftCached.drop 134) (PairLightPrepared6.leftRows.drop 134)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0147
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0134

end D1Bound5.PairLightAdaptivePrepared6
end
