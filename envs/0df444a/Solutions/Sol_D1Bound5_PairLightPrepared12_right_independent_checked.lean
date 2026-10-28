-- Prove2me | solution 1 for D1Bound5.PairLightPrepared12.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:44.88624+00:00
-- url     : https://prove2.me/submissions/9000790d-a5b8-41f5-9a30-b42a72d4a313

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_005
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_006
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared12.rightCached002 PairLightAdaptivePrepared12.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared12.rightCached001 PairLightAdaptivePrepared12.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 221
      PairLightAdaptivePrepared12.rightCached001 PairLightAdaptivePrepared12.rightRows001
      PairLightAdaptivePrepared12.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared12.rightCached000 PairLightAdaptivePrepared12.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 138
      PairLightAdaptivePrepared12.rightCached000 PairLightAdaptivePrepared12.rightRows000
      PairLightAdaptivePrepared12.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared12
end
