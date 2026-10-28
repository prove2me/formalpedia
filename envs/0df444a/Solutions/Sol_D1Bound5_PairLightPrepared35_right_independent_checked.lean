-- Prove2me | solution 1 for D1Bound5.PairLightPrepared35.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:47:50.740869+00:00
-- url     : https://prove2.me/submissions/c966bf36-7a82-4cc4-a387-22ee09689fca

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared35.rightCached002 PairLightAdaptivePrepared35.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared35.rightCached001 PairLightAdaptivePrepared35.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 236
      PairLightAdaptivePrepared35.rightCached001 PairLightAdaptivePrepared35.rightRows001
      PairLightAdaptivePrepared35.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared35.rightCached000 PairLightAdaptivePrepared35.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 132
      PairLightAdaptivePrepared35.rightCached000 PairLightAdaptivePrepared35.rightRows000
      PairLightAdaptivePrepared35.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared35
end
