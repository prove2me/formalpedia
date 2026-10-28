-- Prove2me | solution 1 for D1Bound5.PairLightPrepared35.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:39:46.610063+00:00
-- url     : https://prove2.me/submissions/6b0c5183-84f6-4992-8910-be3a9368f6d7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared35.leftCached002 PairLightAdaptivePrepared35.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared35.leftCached001 PairLightAdaptivePrepared35.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 237
      PairLightAdaptivePrepared35.leftCached001 PairLightAdaptivePrepared35.leftRows001
      PairLightAdaptivePrepared35.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared35.leftCached000 PairLightAdaptivePrepared35.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 132
      PairLightAdaptivePrepared35.leftCached000 PairLightAdaptivePrepared35.leftRows000
      PairLightAdaptivePrepared35.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared35
end
