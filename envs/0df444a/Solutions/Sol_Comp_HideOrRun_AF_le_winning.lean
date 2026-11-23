-- Prove2me | solution 1 for Comp.HideOrRun.AF_le_winning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:51.948919+00:00
-- url     : https://prove2.me/submissions/2519daf9-72e2-48a7-b0d9-63efbe0bfb66

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_afInner_at_univ
import Theorems.Thm_Comp_CsgQ_AF_le_of_step
import Theorems.Thm_Comp_CsgQ_AF_le_univ


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution : (game.toCSG game_wf).AF ↑target ≤ (↑winning : Set HR) :=
  CsgQ.AF_le_of_step game game_wf target Finset.univ winning afInner_at_univ
    (CsgQ.AF_le_univ game game_wf target)
end Comp.HideOrRun
