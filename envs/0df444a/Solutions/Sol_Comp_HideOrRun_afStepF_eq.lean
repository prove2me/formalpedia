-- Prove2me | solution 1 for Comp.HideOrRun.afStepF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:39.263815+00:00
-- url     : https://prove2.me/submissions/83b556c8-fa08-4976-97df-a6f16dbf7764

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_apre1F_eq_apre1C

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution (b y : Finset HR) : game.afStepF b y = afStepC b y := by
  funext x
  change game.apre1F x y ∪ b = apre1C x y ∪ b
  rw [apre1F_eq_apre1C]
end Comp.HideOrRun
