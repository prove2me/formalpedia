-- Prove2me | solution 1 for Csg.skirmish_hide_mem_LF_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:37.990805+00:00
-- url     : https://prove2.me/submissions/39a254a5-f82f-4eb4-8b8f-8e29d169d558

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_LFOuter_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.LF ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.LFOuter ({SkirmishPos.home} : Set SkirmishPos)).le_gfp
    skirmish_safe_le_LFOuter_safe (by decide)
end Csg
