-- Prove2me | solution 1 for Csg.skirmish_AF_home_le_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:35.14407+00:00
-- url     : https://prove2.me/submissions/eab11f4a-049a-469a-99e5-d82c54da59c1

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_gfp_le_map_map_top
import Theorems.Thm_Csg_skirmish_AFOuter_top_le_safe
import Theorems.Thm_Csg_skirmish_AFOuter_safe_le_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.AF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by
  have hstep : skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos)
      (skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) :=
    ((skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos)).mono
      skirmish_AFOuter_top_le_safe).trans skirmish_AFOuter_safe_le_home
  exact (OrderHom.gfp_le_map_map_top
      (skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos))).trans hstep
end Csg
