-- Prove2me | solution 1 for Csg.skirmish_SGFOuter_top_le_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:18:18.721905+00:00
-- url     : https://prove2.me/submissions/34dbb9f1-93ea-4d5d-830d-34590c4a3518

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_SGFInnerFun_top_safe_subset

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe :=
  (skirmishCSG.SGFInner ({SkirmishPos.home} : Set SkirmishPos) ⊤).lfp_le
    skirmish_SGFInnerFun_top_safe_subset
end Csg
