-- Prove2me | solution 1 for D1Bound5.PairLightPrepared14.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:46:07.352994+00:00
-- url     : https://prove2.me/submissions/baa2ca36-defe-47c0-ac6a-23680ac979e8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 2 sieve leftCached leftRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.leftCached004 PairLightAdaptivePrepared14.leftRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.leftCached003 PairLightAdaptivePrepared14.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 76
      PairLightAdaptivePrepared14.leftCached003 PairLightAdaptivePrepared14.leftRows003
      PairLightAdaptivePrepared14.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.leftCached002 PairLightAdaptivePrepared14.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 217
      PairLightAdaptivePrepared14.leftCached002 PairLightAdaptivePrepared14.leftRows002
      PairLightAdaptivePrepared14.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.leftCached001 PairLightAdaptivePrepared14.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 114
      PairLightAdaptivePrepared14.leftCached001 PairLightAdaptivePrepared14.leftRows001
      PairLightAdaptivePrepared14.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.leftCached000 PairLightAdaptivePrepared14.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 88
      PairLightAdaptivePrepared14.leftCached000 PairLightAdaptivePrepared14.leftRows000
      PairLightAdaptivePrepared14.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared14
end
