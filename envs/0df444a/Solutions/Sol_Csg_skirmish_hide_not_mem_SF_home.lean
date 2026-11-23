-- Prove2me | solution 1 for Csg.skirmish_hide_not_mem_SF_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:15.267207+00:00
-- url     : https://prove2.me/submissions/9d85f18e-fefb-4d2e-81cf-020746faa1a3

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishReachGoal_eq_SF

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    SkirmishPos.hide ∉ skirmishCSG.SF ({SkirmishPos.home} : Set SkirmishPos) := by
  rw [skirmishReachGoal_eq_SF]
  intro h
  exact absurd (Set.eq_of_mem_singleton h) (by decide)
end Csg
