-- Prove2me | solution 1 for Csg.reduceMin_hiderC_stageGame_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:31.047819+00:00
-- url     : https://prove2.me/submissions/0b6796ed-33dd-4b1c-9e72-4458cf365970

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
import Theorems.Thm_Csg_combine_hiderC_hider
import Theorems.Thm_Csg_combine_hiderC_thrower

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) :
    (skirmishNCSG.reduceMin hiderC).stageGame .hide v =
      ((skirmishMinCSG.stageGame .hide v).relabelRow hiderSingletonEquiv).relabelCol
        throwerComplementEquiv := by
  have hA : ((skirmishNCSG.reduceMin hiderC).stageGame .hide v).A =
      (((skirmishMinCSG.stageGame .hide v).relabelRow hiderSingletonEquiv).relabelCol
        throwerComplementEquiv).A := by
    funext aC aC'
    change jointR .hide (NCSG.combine hiderC aC aC' .hider) (NCSG.combine hiderC aC aC' .thrower) +
        ∑ s', (jointK .hide (NCSG.combine hiderC aC aC' .hider)
          (NCSG.combine hiderC aC aC' .thrower) s').toReal * v s' =
      jointR .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') +
        ∑ s', (jointK .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') s').toReal * v s'
    rw [combine_hiderC_hider, combine_hiderC_thrower]
  exact congrArg MatrixGame.mk hA
end Csg
