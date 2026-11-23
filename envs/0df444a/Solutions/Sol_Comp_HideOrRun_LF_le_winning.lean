-- Prove2me | solution 1 for Comp.HideOrRun.LF_le_winning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:57:04.651699+00:00
-- url     : https://prove2.me/submissions/4cbf7ae5-2bc6-4b4e-9ec9-2c0239777574

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_inner_at_univ
import Theorems.Thm_Comp_CsgQ_LF_le_of_step
import Theorems.Thm_Comp_CsgQ_LF_le_univ


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution : (game.toCSG game_wf).LF ↑target ≤ (↑winning : Set HR) :=
  CsgQ.LF_le_of_step game game_wf target Finset.univ winning inner_at_univ
    (CsgQ.LF_le_univ game game_wf target)
end Comp.HideOrRun
