-- Prove2me | solution 1 for Csg.skirmish_hide_not_mem_SGF_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:46.53113+00:00
-- url     : https://prove2.me/submissions/9f59517e-13bb-465d-a18f-1de778cfcb70

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_SGF_home_le_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∉ skirmishCSG.SGF ({SkirmishPos.home} : Set SkirmishPos) := by
  intro hmem
  exact absurd (Set.eq_of_mem_singleton (skirmish_SGF_home_le_home hmem)) (by decide)
end Csg
