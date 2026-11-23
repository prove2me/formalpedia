-- Prove2me | solution 1 for Csg.value_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:56.235312+00:00
-- url     : https://prove2.me/submissions/d16102de-a9e1-4e7a-a247-6abdb88a53bd

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
import Theorems.Thm_Csg_stageValue_min_eq
import Theorems.Thm_Csg_stageValue_max_eq

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (vMin vMax : SkirmishState → ℝ)
    (vMinHide : vMin .hide = 4 / 5) (vMinHome : vMin .home = 1) (vMinWet : vMin .wet = 0)
    (vMaxHide : vMax .hide = 1 / 2) (vMaxHome : vMax .home = 1) (vMaxWet : vMax .wet = 0) :
    (skirmishMaxCSG.stageGame .hide vMax).value ≠ (skirmishMinCSG.stageGame .hide vMin).value := by
  rw [stageValue_max_eq vMax vMaxHide vMaxHome vMaxWet,
    stageValue_min_eq vMin vMinHide vMinHome vMinWet]
  norm_num
end Csg
