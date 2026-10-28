-- Prove2me | solution 1 for D1Bound5.PairLightPrepared28.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:37.545983+00:00
-- url     : https://prove2.me/submissions/3b4257af-a197-43dd-be51-59ff4d2fa552

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.leftCached004 PairLightAdaptivePrepared28.leftRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.leftCached003 PairLightAdaptivePrepared28.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 189
      PairLightAdaptivePrepared28.leftCached003 PairLightAdaptivePrepared28.leftRows003
      PairLightAdaptivePrepared28.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.leftCached002 PairLightAdaptivePrepared28.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 151
      PairLightAdaptivePrepared28.leftCached002 PairLightAdaptivePrepared28.leftRows002
      PairLightAdaptivePrepared28.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.leftCached001 PairLightAdaptivePrepared28.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 102
      PairLightAdaptivePrepared28.leftCached001 PairLightAdaptivePrepared28.leftRows001
      PairLightAdaptivePrepared28.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.leftCached000 PairLightAdaptivePrepared28.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 82
      PairLightAdaptivePrepared28.leftCached000 PairLightAdaptivePrepared28.leftRows000
      PairLightAdaptivePrepared28.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared28
end
