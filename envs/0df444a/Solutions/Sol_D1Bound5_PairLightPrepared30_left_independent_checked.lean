-- Prove2me | solution 1 for D1Bound5.PairLightPrepared30.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:45.984614+00:00
-- url     : https://prove2.me/submissions/e78d9e54-2508-42e0-9ff3-0f161c21404f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.leftCached003 PairLightAdaptivePrepared30.leftRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.leftCached002 PairLightAdaptivePrepared30.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 270
      PairLightAdaptivePrepared30.leftCached002 PairLightAdaptivePrepared30.leftRows002
      PairLightAdaptivePrepared30.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.leftCached001 PairLightAdaptivePrepared30.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 121
      PairLightAdaptivePrepared30.leftCached001 PairLightAdaptivePrepared30.leftRows001
      PairLightAdaptivePrepared30.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.leftCached000 PairLightAdaptivePrepared30.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 91
      PairLightAdaptivePrepared30.leftCached000 PairLightAdaptivePrepared30.leftRows000
      PairLightAdaptivePrepared30.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared30
end
