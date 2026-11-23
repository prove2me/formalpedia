-- Prove2me | solution 1 for Csg.skirmish_AGFOuter_top_le_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:38.531023+00:00
-- url     : https://prove2.me/submissions/327a9a01-afa4-404c-94c8-eb23f8a397e4

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_AGFInnerFun_top_safe_subset

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe :=
  (skirmishCSG.AGFInner ({SkirmishPos.home} : Set SkirmishPos) ⊤).lfp_le
    skirmish_AGFInnerFun_top_safe_subset
end Csg
