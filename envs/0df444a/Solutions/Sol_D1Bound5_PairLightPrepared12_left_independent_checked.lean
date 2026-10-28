-- Prove2me | solution 1 for D1Bound5.PairLightPrepared12.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:40:39.977749+00:00
-- url     : https://prove2.me/submissions/aba1c8f6-e8ac-4cce-9b9b-b6fa2ef347ef

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared12.leftCached002 PairLightAdaptivePrepared12.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared12.leftCached001 PairLightAdaptivePrepared12.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 221
      PairLightAdaptivePrepared12.leftCached001 PairLightAdaptivePrepared12.leftRows001
      PairLightAdaptivePrepared12.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared12.leftCached000 PairLightAdaptivePrepared12.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 138
      PairLightAdaptivePrepared12.leftCached000 PairLightAdaptivePrepared12.leftRows000
      PairLightAdaptivePrepared12.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared12
end
