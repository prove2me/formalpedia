-- Prove2me | solution 1 for D1Bound5.PairLightPrepared45.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:55.401423+00:00
-- url     : https://prove2.me/submissions/821673d1-0685-409d-93bd-1a7894b8f463

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_right_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 5 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.rightCached003 PairLightAdaptivePrepared45.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.rightCached002 PairLightAdaptivePrepared45.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 5 sieve 103
      PairLightAdaptivePrepared45.rightCached002 PairLightAdaptivePrepared45.rightRows002
      PairLightAdaptivePrepared45.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.rightCached001 PairLightAdaptivePrepared45.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 5 sieve 60
      PairLightAdaptivePrepared45.rightCached001 PairLightAdaptivePrepared45.rightRows001
      PairLightAdaptivePrepared45.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 5 sieve
      PairLightAdaptivePrepared45.rightCached000 PairLightAdaptivePrepared45.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 5 sieve 43
      PairLightAdaptivePrepared45.rightCached000 PairLightAdaptivePrepared45.rightRows000
      PairLightAdaptivePrepared45.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared45
end
