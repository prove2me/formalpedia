-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:12.474781+00:00
-- url     : https://prove2.me/submissions/cee323cd-acd0-4a90-a286-ffb4159c9357

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 147
      (PairLightPrepared19.rightCached.drop 101) (PairLightPrepared19.rightRows.drop 101) = true := by
  have h245 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 3
      (PairLightPrepared19.rightCached.drop 245) (PairLightPrepared19.rightRows.drop 245) = true := right_prefix_001_part06_checked
  have h221 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 27
      (PairLightPrepared19.rightCached.drop 221) (PairLightPrepared19.rightRows.drop 221) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 3
      (PairLightPrepared19.rightCached.drop 221) (PairLightPrepared19.rightRows.drop 221)
    · exact right_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h245
  have h197 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 51
      (PairLightPrepared19.rightCached.drop 197) (PairLightPrepared19.rightRows.drop 197) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 27
      (PairLightPrepared19.rightCached.drop 197) (PairLightPrepared19.rightRows.drop 197)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h221
  have h173 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 75
      (PairLightPrepared19.rightCached.drop 173) (PairLightPrepared19.rightRows.drop 173) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 51
      (PairLightPrepared19.rightCached.drop 173) (PairLightPrepared19.rightRows.drop 173)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h197
  have h149 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 99
      (PairLightPrepared19.rightCached.drop 149) (PairLightPrepared19.rightRows.drop 149) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 75
      (PairLightPrepared19.rightCached.drop 149) (PairLightPrepared19.rightRows.drop 149)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h173
  have h125 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 123
      (PairLightPrepared19.rightCached.drop 125) (PairLightPrepared19.rightRows.drop 125) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 99
      (PairLightPrepared19.rightCached.drop 125) (PairLightPrepared19.rightRows.drop 125)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h149
  have h101 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 147
      (PairLightPrepared19.rightCached.drop 101) (PairLightPrepared19.rightRows.drop 101) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 123
      (PairLightPrepared19.rightCached.drop 101) (PairLightPrepared19.rightRows.drop 101)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h125
  exact h101
end D1Bound5.PairLightAdaptivePrepared19
end
