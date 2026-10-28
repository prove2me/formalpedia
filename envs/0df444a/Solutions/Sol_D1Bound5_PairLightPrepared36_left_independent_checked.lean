-- Prove2me | solution 1 for D1Bound5.PairLightPrepared36.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:05.75189+00:00
-- url     : https://prove2.me/submissions/a1bbb2d1-25e6-457f-b5cd-001eca2c3d20

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.leftCached004 PairLightAdaptivePrepared36.leftRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.leftCached003 PairLightAdaptivePrepared36.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 275
      PairLightAdaptivePrepared36.leftCached003 PairLightAdaptivePrepared36.leftRows003
      PairLightAdaptivePrepared36.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.leftCached002 PairLightAdaptivePrepared36.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 119
      PairLightAdaptivePrepared36.leftCached002 PairLightAdaptivePrepared36.leftRows002
      PairLightAdaptivePrepared36.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.leftCached001 PairLightAdaptivePrepared36.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 91
      PairLightAdaptivePrepared36.leftCached001 PairLightAdaptivePrepared36.leftRows001
      PairLightAdaptivePrepared36.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.leftCached000 PairLightAdaptivePrepared36.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 76
      PairLightAdaptivePrepared36.leftCached000 PairLightAdaptivePrepared36.leftRows000
      PairLightAdaptivePrepared36.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared36
end
