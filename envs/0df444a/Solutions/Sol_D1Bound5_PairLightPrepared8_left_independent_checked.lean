-- Prove2me | solution 1 for D1Bound5.PairLightPrepared8.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:48:43.493026+00:00
-- url     : https://prove2.me/submissions/eb16e6cb-1bb6-49a2-a2a2-464dc516b103

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h007 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached007 PairLightAdaptivePrepared8.leftRows007 = true := by
    rfl
  have h006 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached006 PairLightAdaptivePrepared8.leftRows006 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 189
      PairLightAdaptivePrepared8.leftCached006 PairLightAdaptivePrepared8.leftRows006
      PairLightAdaptivePrepared8.left_prefix_006_checked h007
  have h005 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached005 PairLightAdaptivePrepared8.leftRows005 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 151
      PairLightAdaptivePrepared8.leftCached005 PairLightAdaptivePrepared8.leftRows005
      PairLightAdaptivePrepared8.left_prefix_005_checked h006
  have h004 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached004 PairLightAdaptivePrepared8.leftRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 102
      PairLightAdaptivePrepared8.leftCached004 PairLightAdaptivePrepared8.leftRows004
      PairLightAdaptivePrepared8.left_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached003 PairLightAdaptivePrepared8.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 82
      PairLightAdaptivePrepared8.leftCached003 PairLightAdaptivePrepared8.leftRows003
      PairLightAdaptivePrepared8.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached002 PairLightAdaptivePrepared8.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 71
      PairLightAdaptivePrepared8.leftCached002 PairLightAdaptivePrepared8.leftRows002
      PairLightAdaptivePrepared8.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached001 PairLightAdaptivePrepared8.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 63
      PairLightAdaptivePrepared8.leftCached001 PairLightAdaptivePrepared8.leftRows001
      PairLightAdaptivePrepared8.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared8.leftCached000 PairLightAdaptivePrepared8.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 58
      PairLightAdaptivePrepared8.leftCached000 PairLightAdaptivePrepared8.leftRows000
      PairLightAdaptivePrepared8.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared8
end
