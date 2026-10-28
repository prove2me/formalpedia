-- Prove2me | solution 1 for D1Bound5.PairLightPrepared28.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:52:49.827443+00:00
-- url     : https://prove2.me/submissions/330232e4-183b-4a34-a383-3c53e7692a67

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.rightCached004 PairLightAdaptivePrepared28.rightRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.rightCached003 PairLightAdaptivePrepared28.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 189
      PairLightAdaptivePrepared28.rightCached003 PairLightAdaptivePrepared28.rightRows003
      PairLightAdaptivePrepared28.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.rightCached002 PairLightAdaptivePrepared28.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 151
      PairLightAdaptivePrepared28.rightCached002 PairLightAdaptivePrepared28.rightRows002
      PairLightAdaptivePrepared28.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.rightCached001 PairLightAdaptivePrepared28.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 102
      PairLightAdaptivePrepared28.rightCached001 PairLightAdaptivePrepared28.rightRows001
      PairLightAdaptivePrepared28.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared28.rightCached000 PairLightAdaptivePrepared28.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 82
      PairLightAdaptivePrepared28.rightCached000 PairLightAdaptivePrepared28.rightRows000
      PairLightAdaptivePrepared28.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared28
end
