-- Prove2me | solution 1 for Csg.skirmish_A_empty_safe_le_LFV_empty_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:58.1928+00:00
-- url     : https://prove2.me/submissions/bc789652-b831-4da0-b113-a23b01f9c851

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_LFW_empty_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : SkirmishPos) :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s ≤
      skirmishCSG.LFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s := by
  apply (skirmishCSG.LFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s).le_gfp
  change skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s ≤
      skirmishCSG.LFW (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s)
        (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
  exact le_of_eq
    (skirmish_LFW_empty_safe_safe (skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s) s).symm
end Csg
