-- Prove2me | solution 1 for D1Bound5.PairLightPrepared8.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:51:59.24493+00:00
-- url     : https://prove2.me/submissions/a00da1fd-3d88-4bba-9660-6a3e160b348d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_006_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by
  have h007 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached007 PairLightAdaptivePrepared8.rightRows007 = true := by
    rfl
  have h006 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached006 PairLightAdaptivePrepared8.rightRows006 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 194
      PairLightAdaptivePrepared8.rightCached006 PairLightAdaptivePrepared8.rightRows006
      PairLightAdaptivePrepared8.right_prefix_006_checked h007
  have h005 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached005 PairLightAdaptivePrepared8.rightRows005 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 149
      PairLightAdaptivePrepared8.rightCached005 PairLightAdaptivePrepared8.rightRows005
      PairLightAdaptivePrepared8.right_prefix_005_checked h006
  have h004 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached004 PairLightAdaptivePrepared8.rightRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 101
      PairLightAdaptivePrepared8.rightCached004 PairLightAdaptivePrepared8.rightRows004
      PairLightAdaptivePrepared8.right_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached003 PairLightAdaptivePrepared8.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 82
      PairLightAdaptivePrepared8.rightCached003 PairLightAdaptivePrepared8.rightRows003
      PairLightAdaptivePrepared8.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached002 PairLightAdaptivePrepared8.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 71
      PairLightAdaptivePrepared8.rightCached002 PairLightAdaptivePrepared8.rightRows002
      PairLightAdaptivePrepared8.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached001 PairLightAdaptivePrepared8.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 63
      PairLightAdaptivePrepared8.rightCached001 PairLightAdaptivePrepared8.rightRows001
      PairLightAdaptivePrepared8.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.rightCached000 PairLightAdaptivePrepared8.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 58
      PairLightAdaptivePrepared8.rightCached000 PairLightAdaptivePrepared8.rightRows000
      PairLightAdaptivePrepared8.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared8
end
