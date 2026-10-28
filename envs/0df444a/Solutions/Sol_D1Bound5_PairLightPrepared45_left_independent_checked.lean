-- Prove2me | solution 1 for D1Bound5.PairLightPrepared45.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:41:39.125322+00:00
-- url     : https://prove2.me/submissions/8981cfa4-c507-40ff-98a9-8d6b5de75e35

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 5 sieve leftCached leftRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.leftCached003 PairLightAdaptivePrepared45.leftRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.leftCached002 PairLightAdaptivePrepared45.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 5 sieve 101
      PairLightAdaptivePrepared45.leftCached002 PairLightAdaptivePrepared45.leftRows002
      PairLightAdaptivePrepared45.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.leftCached001 PairLightAdaptivePrepared45.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 5 sieve 61
      PairLightAdaptivePrepared45.leftCached001 PairLightAdaptivePrepared45.leftRows001
      PairLightAdaptivePrepared45.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.leftCached000 PairLightAdaptivePrepared45.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 5 sieve 43
      PairLightAdaptivePrepared45.leftCached000 PairLightAdaptivePrepared45.leftRows000
      PairLightAdaptivePrepared45.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared45
end
