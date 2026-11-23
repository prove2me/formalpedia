-- Prove2me | solution 1 for Comp.HideOrRun.hr_AF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:55:14.717142+00:00
-- url     : https://prove2.me/submissions/3b8325cb-b7b5-43e3-a051-bf558e97a6df

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_AF_le_target
import Theorems.Thm_Comp_HideOrRun_afInner_at_target
import Theorems.Thm_Comp_CsgQ_AF_eq_coe_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution : (game.toCSG game_wf).AF ↑target = (↑target : Set HR) :=
  CsgQ.AF_eq_coe_of_fixed game game_wf target target afInner_at_target AF_le_target
end Comp.HideOrRun
