-- Prove2me | solution 1 for D1Bound5.PairLightPrepared40.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:56:04.351262+00:00
-- url     : https://prove2.me/submissions/04e9f340-1f6e-4f9c-b79f-986f0f29d015

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared40.rightCached002 PairLightAdaptivePrepared40.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared40.rightCached001 PairLightAdaptivePrepared40.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 220
      PairLightAdaptivePrepared40.rightCached001 PairLightAdaptivePrepared40.rightRows001
      PairLightAdaptivePrepared40.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared40.rightCached000 PairLightAdaptivePrepared40.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 138
      PairLightAdaptivePrepared40.rightCached000 PairLightAdaptivePrepared40.rightRows000
      PairLightAdaptivePrepared40.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared40
end
