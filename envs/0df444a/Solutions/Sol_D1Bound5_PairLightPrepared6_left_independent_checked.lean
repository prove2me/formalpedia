-- Prove2me | solution 1 for D1Bound5.PairLightPrepared6.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:19.852829+00:00
-- url     : https://prove2.me/submissions/5f41ea6e-7371-46df-b5c7-03cd494c858e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_004_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h006 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached006 PairLightAdaptivePrepared6.leftRows006 = true := by
    rfl
  have h005 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached005 PairLightAdaptivePrepared6.leftRows005 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 189
      PairLightAdaptivePrepared6.leftCached005 PairLightAdaptivePrepared6.leftRows005
      PairLightAdaptivePrepared6.left_prefix_005_checked h006
  have h004 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached004 PairLightAdaptivePrepared6.leftRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 151
      PairLightAdaptivePrepared6.leftCached004 PairLightAdaptivePrepared6.leftRows004
      PairLightAdaptivePrepared6.left_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached003 PairLightAdaptivePrepared6.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 102
      PairLightAdaptivePrepared6.leftCached003 PairLightAdaptivePrepared6.leftRows003
      PairLightAdaptivePrepared6.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached002 PairLightAdaptivePrepared6.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 82
      PairLightAdaptivePrepared6.leftCached002 PairLightAdaptivePrepared6.leftRows002
      PairLightAdaptivePrepared6.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached001 PairLightAdaptivePrepared6.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 71
      PairLightAdaptivePrepared6.leftCached001 PairLightAdaptivePrepared6.leftRows001
      PairLightAdaptivePrepared6.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared6.leftCached000 PairLightAdaptivePrepared6.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 63
      PairLightAdaptivePrepared6.leftCached000 PairLightAdaptivePrepared6.leftRows000
      PairLightAdaptivePrepared6.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared6
end
