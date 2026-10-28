-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared23.all_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:24:21.548264+00:00
-- url     : https://prove2.me/submissions/87654c9e-1970-4496-b058-84c23d7147a0

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk00_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk01_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk02_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk03_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk04_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk05_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk06_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk07_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk08_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk09_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk10_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk11_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk12_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk13_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk14_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk15_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_of_prefix_drop

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      witnesses destinations = true := by
  have h0964 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 964) (destinations.drop 964) = true := by
    rfl
  have h0960 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 960) (destinations.drop 960) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 4
      (witnesses.drop 960) (destinations.drop 960) chunk15_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0964
  have h0896 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 896) (destinations.drop 896) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 896) (destinations.drop 896) chunk14_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0960
  have h0832 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 832) (destinations.drop 832) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 832) (destinations.drop 832) chunk13_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0896
  have h0768 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 768) (destinations.drop 768) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 768) (destinations.drop 768) chunk12_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0832
  have h0704 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 704) (destinations.drop 704) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 704) (destinations.drop 704) chunk11_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0768
  have h0640 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 640) (destinations.drop 640) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 640) (destinations.drop 640) chunk10_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0704
  have h0576 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 576) (destinations.drop 576) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 576) (destinations.drop 576) chunk09_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0640
  have h0512 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 512) (destinations.drop 512) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) chunk08_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0576
  have h0448 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 448) (destinations.drop 448) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 448) (destinations.drop 448) chunk07_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0512
  have h0384 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 384) (destinations.drop 384) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 384) (destinations.drop 384) chunk06_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0448
  have h0320 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 320) (destinations.drop 320) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) chunk05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0384
  have h0256 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 256) (destinations.drop 256) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 256) (destinations.drop 256) chunk04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0320
  have h0192 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 192) (destinations.drop 192) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 192) (destinations.drop 192) chunk03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0256
  have h0128 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 128) (destinations.drop 128) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 128) (destinations.drop 128) chunk02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0192
  have h0064 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 64) (destinations.drop 64) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 64) (destinations.drop 64) chunk01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0128
  have h0000 : pairLightIndexedWitnessesCheckedBool 1 1 a b anchorRoot (10^1100) vertices
      (witnesses.drop 0) (destinations.drop 0) = true := by
    apply pairLightIndexedWitnessesCheckedBool_of_prefix_drop 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 0) (destinations.drop 0) chunk00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h0064
  simpa only [List.drop_zero] using h0000

end D1Bound5.PairLightClosurePrepared23
end
