-- Prove2me | solution 1 for Comp.HideOrRun.hr_LF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:59:27.362065+00:00
-- url     : https://prove2.me/submissions/ad066b4a-4956-4ae7-ad79-98af0dfad368

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_LF_le_winning
import Theorems.Thm_Comp_HideOrRun_inner_at_winning
import Theorems.Thm_Comp_CsgQ_LF_eq_coe_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution : (game.toCSG game_wf).LF ↑target = (↑winning : Set HR) :=
  CsgQ.LF_eq_coe_of_fixed game game_wf target winning inner_at_winning LF_le_winning
end Comp.HideOrRun
