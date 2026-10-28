-- Prove2me | solution 1 for D1Bound5.PairLightPrepared4.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:56:01.120672+00:00
-- url     : https://prove2.me/submissions/a2435bb9-1aed-4cca-b2b4-ff94151efb02

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h005 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared4.leftCached005 PairLightAdaptivePrepared4.leftRows005 = true := by
    rfl
  have h004 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared4.leftCached004 PairLightAdaptivePrepared4.leftRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 191
      PairLightAdaptivePrepared4.leftCached004 PairLightAdaptivePrepared4.leftRows004
      PairLightAdaptivePrepared4.left_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared4.leftCached003 PairLightAdaptivePrepared4.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 150
      PairLightAdaptivePrepared4.leftCached003 PairLightAdaptivePrepared4.leftRows003
      PairLightAdaptivePrepared4.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared4.leftCached002 PairLightAdaptivePrepared4.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 102
      PairLightAdaptivePrepared4.leftCached002 PairLightAdaptivePrepared4.leftRows002
      PairLightAdaptivePrepared4.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared4.leftCached001 PairLightAdaptivePrepared4.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 82
      PairLightAdaptivePrepared4.leftCached001 PairLightAdaptivePrepared4.leftRows001
      PairLightAdaptivePrepared4.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared4.leftCached000 PairLightAdaptivePrepared4.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 71
      PairLightAdaptivePrepared4.leftCached000 PairLightAdaptivePrepared4.leftRows000
      PairLightAdaptivePrepared4.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared4
end
