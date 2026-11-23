-- Prove2me | solution 1 for Csg.skirmish_hide_mem_LGF_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:56.726802+00:00
-- url     : https://prove2.me/submissions/969eaa6d-83e1-4d58-a14b-629cc1b57e23

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_le_LGFOuter_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∈ skirmishCSG.LGF ({SkirmishPos.home} : Set SkirmishPos) :=
  (skirmishCSG.LGFOuter ({SkirmishPos.home} : Set SkirmishPos)).le_gfp
    skirmish_safe_le_LGFOuter_safe (by decide)
end Csg
