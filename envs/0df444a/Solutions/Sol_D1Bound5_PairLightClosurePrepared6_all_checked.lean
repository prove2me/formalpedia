-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared6.all_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:06.512078+00:00
-- url     : https://prove2.me/submissions/7365f86f-a756-4bb4-9567-dba35a7398e4

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk00_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk01_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk02_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk03_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk04_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk05_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk06_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk07_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk08_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk09_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk10_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk11_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk12_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk13_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk14_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk15_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk16_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk17_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk18_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk19_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk20_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_of_prefix_drop

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      witnesses destinations = true := by
  have h1318 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1318) (destinations.drop 1318) = true := by
    rfl
  have h1280 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1280) (destinations.drop 1280) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 38
      (witnesses.drop 1280) (destinations.drop 1280) chunk20_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1318
  have h1216 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1216) (destinations.drop 1216) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1216) (destinations.drop 1216) chunk19_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1280
  have h1152 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1152) (destinations.drop 1152) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1152) (destinations.drop 1152) chunk18_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1216
  have h1088 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1088) (destinations.drop 1088) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1088) (destinations.drop 1088) chunk17_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1152
  have h1024 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1024) (destinations.drop 1024) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1024) (destinations.drop 1024) chunk16_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1088
  have h0960 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 960) (destinations.drop 960) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 960) (destinations.drop 960) chunk15_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1024
  have h0896 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 896) (destinations.drop 896) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 896) (destinations.drop 896) chunk14_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0960
  have h0832 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 832) (destinations.drop 832) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 832) (destinations.drop 832) chunk13_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0896
  have h0768 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 768) (destinations.drop 768) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 768) (destinations.drop 768) chunk12_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0832
  have h0704 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 704) (destinations.drop 704) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 704) (destinations.drop 704) chunk11_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0768
  have h0640 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 640) (destinations.drop 640) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 640) (destinations.drop 640) chunk10_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0704
  have h0576 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 576) (destinations.drop 576) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 576) (destinations.drop 576) chunk09_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0640
  have h0512 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 512) (destinations.drop 512) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) chunk08_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0576
  have h0448 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 448) (destinations.drop 448) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 448) (destinations.drop 448) chunk07_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0512
  have h0384 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 384) (destinations.drop 384) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 384) (destinations.drop 384) chunk06_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0448
  have h0320 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 320) (destinations.drop 320) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) chunk05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0384
  have h0256 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 256) (destinations.drop 256) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 256) (destinations.drop 256) chunk04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0320
  have h0192 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 192) (destinations.drop 192) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 192) (destinations.drop 192) chunk03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0256
  have h0128 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 128) (destinations.drop 128) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 128) (destinations.drop 128) chunk02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0192
  have h0064 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 64) (destinations.drop 64) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 64) (destinations.drop 64) chunk01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0128
  have h0000 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 0) (destinations.drop 0) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 0) (destinations.drop 0) chunk00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0064
  simpa only [List.drop_zero] using h0000

end D1Bound5.PairLightClosurePrepared6
end
