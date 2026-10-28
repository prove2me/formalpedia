-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared8.all_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:18.073998+00:00
-- url     : https://prove2.me/submissions/c8683157-7db2-48c4-ac1c-071234517777

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk00_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk01_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk02_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk03_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk04_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk05_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk06_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk07_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk08_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk09_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk10_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk11_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk12_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk13_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk14_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk15_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk16_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk17_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk18_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk19_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk20_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk21_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk22_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_of_prefix_drop

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      witnesses destinations = true := by
  have h1437 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1437) (destinations.drop 1437) = true := by
    rfl
  have h1408 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1408) (destinations.drop 1408) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 29
      (witnesses.drop 1408) (destinations.drop 1408) chunk22_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1437
  have h1344 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1344) (destinations.drop 1344) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1344) (destinations.drop 1344) chunk21_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1408
  have h1280 : pairLightIndexedWitnessesCheckedBool 0 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 1280) (destinations.drop 1280) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1280) (destinations.drop 1280) chunk20_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h1344
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

end D1Bound5.PairLightClosurePrepared8
end
