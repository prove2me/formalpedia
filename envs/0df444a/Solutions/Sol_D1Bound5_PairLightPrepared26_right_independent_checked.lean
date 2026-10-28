-- Prove2me | solution 1 for D1Bound5.PairLightPrepared26.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:53:45.329167+00:00
-- url     : https://prove2.me/submissions/a44ba1bd-4506-4230-8a59-ed726b66e47c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_008
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_010
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_005_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h008 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached008 PairLightAdaptivePrepared26.rightRows008 = true := by
    rfl
  have h007 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached007 PairLightAdaptivePrepared26.rightRows007 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 145
      PairLightAdaptivePrepared26.rightCached007 PairLightAdaptivePrepared26.rightRows007
      PairLightAdaptivePrepared26.right_prefix_007_checked h008
  have h006 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached006 PairLightAdaptivePrepared26.rightRows006 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 173
      PairLightAdaptivePrepared26.rightCached006 PairLightAdaptivePrepared26.rightRows006
      PairLightAdaptivePrepared26.right_prefix_006_checked h007
  have h005 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached005 PairLightAdaptivePrepared26.rightRows005 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 107
      PairLightAdaptivePrepared26.rightCached005 PairLightAdaptivePrepared26.rightRows005
      PairLightAdaptivePrepared26.right_prefix_005_checked h006
  have h004 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached004 PairLightAdaptivePrepared26.rightRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 85
      PairLightAdaptivePrepared26.rightCached004 PairLightAdaptivePrepared26.rightRows004
      PairLightAdaptivePrepared26.right_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached003 PairLightAdaptivePrepared26.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 73
      PairLightAdaptivePrepared26.rightCached003 PairLightAdaptivePrepared26.rightRows003
      PairLightAdaptivePrepared26.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached002 PairLightAdaptivePrepared26.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 65
      PairLightAdaptivePrepared26.rightCached002 PairLightAdaptivePrepared26.rightRows002
      PairLightAdaptivePrepared26.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached001 PairLightAdaptivePrepared26.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 59
      PairLightAdaptivePrepared26.rightCached001 PairLightAdaptivePrepared26.rightRows001
      PairLightAdaptivePrepared26.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared26.rightCached000 PairLightAdaptivePrepared26.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 54
      PairLightAdaptivePrepared26.rightCached000 PairLightAdaptivePrepared26.rightRows000
      PairLightAdaptivePrepared26.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared26
end
