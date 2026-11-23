-- Prove2me | solution 1 for Csg.skirmish_hide_mem_LFG_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:45.900232+00:00
-- url     : https://prove2.me/submissions/96d9ae62-dfe9-46c6-81ed-045b0badf058

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_LFGX_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.LFG skirmishSafe :=
  (skirmishCSG.LFGOuter skirmishSafe).le_gfp skirmish_safe_le_LFGX_safe_safe (by decide)
end Csg
