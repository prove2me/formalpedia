-- Prove2me | solution 1 for Comp.HideOrRun.lw_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:43:14.096367+00:00
-- url     : https://prove2.me/submissions/e9562dba-04df-46cc-9441-42b3d0aa99ac

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution : ∀ (x y : Finset HR) (s : HR), lStepC x y s (lwC x y s) = lwC x y s := by
  decide
end Comp.HideOrRun
