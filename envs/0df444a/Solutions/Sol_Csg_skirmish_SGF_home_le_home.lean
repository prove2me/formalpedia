-- Prove2me | solution 1 for Csg.skirmish_SGF_home_le_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:30.747031+00:00
-- url     : https://prove2.me/submissions/62fc7721-c683-4008-8d82-66973139b221

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_gfp_le_map_map_top
import Theorems.Thm_Csg_skirmish_SGFOuter_top_le_safe
import Theorems.Thm_Csg_skirmish_SGFOuter_safe_le_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.SGF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  have hstep : skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos)
      (skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
    ((skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos)).mono
      skirmish_SGFOuter_top_le_safe).trans skirmish_SGFOuter_safe_le_home
  exact (OrderHom.gfp_le_map_map_top
      (skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos))).trans hstep
end Csg
