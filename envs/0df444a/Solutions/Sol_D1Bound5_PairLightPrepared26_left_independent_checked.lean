-- Prove2me | solution 1 for D1Bound5.PairLightPrepared26.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:20.187981+00:00
-- url     : https://prove2.me/submissions/815fe7fe-c803-4da8-9f33-5c02e9edc576

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_004_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_005_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_006_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by
  have h008 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached008 PairLightAdaptivePrepared26.leftRows008 = true := by
    rfl
  have h007 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached007 PairLightAdaptivePrepared26.leftRows007 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 145
      PairLightAdaptivePrepared26.leftCached007 PairLightAdaptivePrepared26.leftRows007
      PairLightAdaptivePrepared26.left_prefix_007_checked h008
  have h006 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached006 PairLightAdaptivePrepared26.leftRows006 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 173
      PairLightAdaptivePrepared26.leftCached006 PairLightAdaptivePrepared26.leftRows006
      PairLightAdaptivePrepared26.left_prefix_006_checked h007
  have h005 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached005 PairLightAdaptivePrepared26.leftRows005 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 107
      PairLightAdaptivePrepared26.leftCached005 PairLightAdaptivePrepared26.leftRows005
      PairLightAdaptivePrepared26.left_prefix_005_checked h006
  have h004 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached004 PairLightAdaptivePrepared26.leftRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 85
      PairLightAdaptivePrepared26.leftCached004 PairLightAdaptivePrepared26.leftRows004
      PairLightAdaptivePrepared26.left_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached003 PairLightAdaptivePrepared26.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 73
      PairLightAdaptivePrepared26.leftCached003 PairLightAdaptivePrepared26.leftRows003
      PairLightAdaptivePrepared26.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached002 PairLightAdaptivePrepared26.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 65
      PairLightAdaptivePrepared26.leftCached002 PairLightAdaptivePrepared26.leftRows002
      PairLightAdaptivePrepared26.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached001 PairLightAdaptivePrepared26.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 59
      PairLightAdaptivePrepared26.leftCached001 PairLightAdaptivePrepared26.leftRows001
      PairLightAdaptivePrepared26.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.leftCached000 PairLightAdaptivePrepared26.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 54
      PairLightAdaptivePrepared26.leftCached000 PairLightAdaptivePrepared26.leftRows000
      PairLightAdaptivePrepared26.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared26
end
