-- Prove2me | solution 1 for D1Bound5.PairLightPrepared40.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:06.773391+00:00
-- url     : https://prove2.me/submissions/2f06d14a-0534-42ef-9c39-448545798925

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared40.leftCached002 PairLightAdaptivePrepared40.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared40.leftCached001 PairLightAdaptivePrepared40.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 223
      PairLightAdaptivePrepared40.leftCached001 PairLightAdaptivePrepared40.leftRows001
      PairLightAdaptivePrepared40.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared40.leftCached000 PairLightAdaptivePrepared40.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 137
      PairLightAdaptivePrepared40.leftCached000 PairLightAdaptivePrepared40.leftRows000
      PairLightAdaptivePrepared40.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared40
end
