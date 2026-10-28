-- Prove2me | solution 1 for D1Bound5.PairLightPrepared10.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:57:24.306+00:00
-- url     : https://prove2.me/submissions/5dbd9ea6-0330-4cc9-bb3e-720e90a0a8f2

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h005 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.leftCached005 PairLightAdaptivePrepared10.leftRows005 = true := by
    rfl
  have h004 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.leftCached004 PairLightAdaptivePrepared10.leftRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 191
      PairLightAdaptivePrepared10.leftCached004 PairLightAdaptivePrepared10.leftRows004
      PairLightAdaptivePrepared10.left_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.leftCached003 PairLightAdaptivePrepared10.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 150
      PairLightAdaptivePrepared10.leftCached003 PairLightAdaptivePrepared10.leftRows003
      PairLightAdaptivePrepared10.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.leftCached002 PairLightAdaptivePrepared10.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 102
      PairLightAdaptivePrepared10.leftCached002 PairLightAdaptivePrepared10.leftRows002
      PairLightAdaptivePrepared10.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.leftCached001 PairLightAdaptivePrepared10.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 82
      PairLightAdaptivePrepared10.leftCached001 PairLightAdaptivePrepared10.leftRows001
      PairLightAdaptivePrepared10.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.leftCached000 PairLightAdaptivePrepared10.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 71
      PairLightAdaptivePrepared10.leftCached000 PairLightAdaptivePrepared10.leftRows000
      PairLightAdaptivePrepared10.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared10
end
