-- Prove2me | solution 1 for Comp.HideOrRun.inner_at_winning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:53:59.937071+00:00
-- url     : https://prove2.me/submissions/f88bcd9a-0766-421b-9e5b-75bd7d2bdf34

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_mid_eq

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution :
    ((game.toCSG game_wf).LFInner ↑target ↑winning).lfp = (↑winning : Set HR) :=
  mid_eq target winning winning 2 (by decide) (by decide)
end Comp.HideOrRun
