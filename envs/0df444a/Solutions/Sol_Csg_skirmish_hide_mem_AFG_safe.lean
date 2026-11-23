-- Prove2me | solution 1 for Csg.skirmish_hide_mem_AFG_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:41.944411+00:00
-- url     : https://prove2.me/submissions/502bf236-e973-412b-abe7-95455b8aeb4b

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_AFGX_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.AFG skirmishSafe :=
  (skirmishCSG.AFGOuter skirmishSafe).le_gfp skirmish_safe_le_AFGX_safe_safe (by decide)
end Csg
