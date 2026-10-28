-- Prove2me | solution 1 for D1Bound5.PairLightPrepared1.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:06.410809+00:00
-- url     : https://prove2.me/submissions/5f3ce37d-606f-43db-82ce-3f76120c32c0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared1.leftCached002 PairLightAdaptivePrepared1.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared1.leftCached001 PairLightAdaptivePrepared1.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 223
      PairLightAdaptivePrepared1.leftCached001 PairLightAdaptivePrepared1.leftRows001
      PairLightAdaptivePrepared1.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared1.leftCached000 PairLightAdaptivePrepared1.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 137
      PairLightAdaptivePrepared1.leftCached000 PairLightAdaptivePrepared1.leftRows000
      PairLightAdaptivePrepared1.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared1
end
