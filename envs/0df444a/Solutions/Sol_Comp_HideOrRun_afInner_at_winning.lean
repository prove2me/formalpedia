-- Prove2me | solution 1 for Comp.HideOrRun.afInner_at_winning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:37.877954+00:00
-- url     : https://prove2.me/submissions/c4b81c64-ef7f-4399-b31f-0371bc1163c6

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_afStepF_eq
import Theorems.Thm_Comp_CsgQ_afInner_eq_coe_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution :
    ((game.toCSG game_wf).AFInner ↑target ↑winning).lfp = (↑target : Set HR) :=
  CsgQ.afInner_eq_coe_of_fixed game game_wf target winning target 1
    (by rw [afStepF_eq]; decide) (by rw [afStepF_eq]; decide)
end Comp.HideOrRun
