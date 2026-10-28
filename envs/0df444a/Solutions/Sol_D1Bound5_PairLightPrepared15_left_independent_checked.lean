-- Prove2me | solution 1 for D1Bound5.PairLightPrepared15.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:45:11.790664+00:00
-- url     : https://prove2.me/submissions/67caeeeb-1be5-48e7-917a-9bbce648ddb1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 2 sieve leftCached leftRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.leftCached003 PairLightAdaptivePrepared15.leftRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.leftCached002 PairLightAdaptivePrepared15.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 267
      PairLightAdaptivePrepared15.leftCached002 PairLightAdaptivePrepared15.leftRows002
      PairLightAdaptivePrepared15.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.leftCached001 PairLightAdaptivePrepared15.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 122
      PairLightAdaptivePrepared15.leftCached001 PairLightAdaptivePrepared15.leftRows001
      PairLightAdaptivePrepared15.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.leftCached000 PairLightAdaptivePrepared15.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 92
      PairLightAdaptivePrepared15.leftCached000 PairLightAdaptivePrepared15.leftRows000
      PairLightAdaptivePrepared15.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared15
end
