-- Prove2me | solution 1 for Comp.HideOrRun.afInner_at_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:46.421989+00:00
-- url     : https://prove2.me/submissions/605d7c15-d779-406f-9d2e-43bb176f36a6

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
    ((game.toCSG game_wf).AFInner ↑target ↑target).lfp = (↑target : Set HR) :=
  CsgQ.afInner_eq_coe_of_fixed game game_wf target target target 1
    (by rw [afStepF_eq]; decide) (by rw [afStepF_eq]; decide)
end Comp.HideOrRun
