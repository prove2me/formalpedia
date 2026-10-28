-- Prove2me | solution 1 for D1Bound5.PairLightPrepared17.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:44:17.570645+00:00
-- url     : https://prove2.me/submissions/1ddeafe5-97fc-43a3-a3a5-4c6279d50dee

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 2 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared17.leftCached002 PairLightAdaptivePrepared17.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared17.leftCached001 PairLightAdaptivePrepared17.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 223
      PairLightAdaptivePrepared17.leftCached001 PairLightAdaptivePrepared17.leftRows001
      PairLightAdaptivePrepared17.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared17.leftCached000 PairLightAdaptivePrepared17.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 137
      PairLightAdaptivePrepared17.leftCached000 PairLightAdaptivePrepared17.leftRows000
      PairLightAdaptivePrepared17.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared17
end
