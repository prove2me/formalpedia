-- Prove2me | solution 1 for D1Bound5.PairLightPrepared48.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:57:18.148992+00:00
-- url     : https://prove2.me/submissions/5bb34541-c4bb-4942-9a82-6fe3d7cd1dc9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 8 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 8 sieve
      PairLightAdaptivePrepared48.leftCached002 PairLightAdaptivePrepared48.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 8 sieve
      PairLightAdaptivePrepared48.leftCached001 PairLightAdaptivePrepared48.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 8 sieve 223
      PairLightAdaptivePrepared48.leftCached001 PairLightAdaptivePrepared48.leftRows001
      PairLightAdaptivePrepared48.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 8 sieve
      PairLightAdaptivePrepared48.leftCached000 PairLightAdaptivePrepared48.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 8 sieve 137
      PairLightAdaptivePrepared48.leftCached000 PairLightAdaptivePrepared48.leftRows000
      PairLightAdaptivePrepared48.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared48
end
