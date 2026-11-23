-- Prove2me | solution 1 for Csg.reduceMax_hiderC_stageGame_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:53.204899+00:00
-- url     : https://prove2.me/submissions/c02d6413-d47f-4ca6-80cc-172b85f02456

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
import Theorems.Thm_Csg_combine_hiderC_hider
import Theorems.Thm_Csg_combine_hiderC_thrower

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) :
    (skirmishNCSG.reduceMax hiderC).stageGame .hide v =
      ((skirmishMaxCSG.stageGame .hide v).relabelRow throwerComplementEquiv).relabelCol
        hiderSingletonEquiv := by
  have hA : ((skirmishNCSG.reduceMax hiderC).stageGame .hide v).A =
      (((skirmishMaxCSG.stageGame .hide v).relabelRow throwerComplementEquiv).relabelCol
        hiderSingletonEquiv).A := by
    funext aC' aC
    change jointR .hide (NCSG.combine hiderC aC aC' .hider) (NCSG.combine hiderC aC aC' .thrower) +
        ∑ s', (jointK .hide (NCSG.combine hiderC aC aC' .hider)
          (NCSG.combine hiderC aC aC' .thrower) s').toReal * v s' =
      jointR .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') +
        ∑ s', (jointK .hide (hiderSingletonEquiv aC) (throwerComplementEquiv aC') s').toReal * v s'
    rw [combine_hiderC_hider, combine_hiderC_thrower]
  exact congrArg MatrixGame.mk hA
end Csg
