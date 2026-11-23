-- Prove2me | solution 1 for Csg.reduceMax_ne_reduceMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:00.402402+00:00
-- url     : https://prove2.me/submissions/5c4e4970-e270-47f9-ba5c-0270e42228c2

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
import Theorems.Thm_Csg_reduceMin_hiderC_stageValue_eq
import Theorems.Thm_Csg_reduceMax_hiderC_stageValue_eq

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (vMin vMax : SkirmishState → ℝ)
    (vMinHide : vMin .hide = 4 / 5) (vMinHome : vMin .home = 1) (vMinWet : vMin .wet = 0)
    (vMaxHide : vMax .hide = 1 / 2) (vMaxHome : vMax .home = 1) (vMaxWet : vMax .wet = 0) :
    (skirmishNCSG.reduceMax hiderC).stageValue .hide vMax ≠
      (skirmishNCSG.reduceMin hiderC).stageValue .hide vMin := by
  rw [reduceMax_hiderC_stageValue_eq vMax vMaxHide vMaxHome vMaxWet,
    reduceMin_hiderC_stageValue_eq vMin vMinHide vMinHome vMinWet]
  norm_num
end Csg
