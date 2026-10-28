-- Prove2me | solution 1 for D1Bound5.PairLightPrepared21.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:26:30.471143+00:00
-- url     : https://prove2.me/submissions/f7a15d42-313b-4a64-ba63-2145a61c93a1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.leftCached004 PairLightAdaptivePrepared21.leftRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.leftCached003 PairLightAdaptivePrepared21.leftRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 189
      PairLightAdaptivePrepared21.leftCached003 PairLightAdaptivePrepared21.leftRows003
      PairLightAdaptivePrepared21.left_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.leftCached002 PairLightAdaptivePrepared21.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 151
      PairLightAdaptivePrepared21.leftCached002 PairLightAdaptivePrepared21.leftRows002
      PairLightAdaptivePrepared21.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.leftCached001 PairLightAdaptivePrepared21.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 102
      PairLightAdaptivePrepared21.leftCached001 PairLightAdaptivePrepared21.leftRows001
      PairLightAdaptivePrepared21.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.leftCached000 PairLightAdaptivePrepared21.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 82
      PairLightAdaptivePrepared21.leftCached000 PairLightAdaptivePrepared21.leftRows000
      PairLightAdaptivePrepared21.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared21
end
