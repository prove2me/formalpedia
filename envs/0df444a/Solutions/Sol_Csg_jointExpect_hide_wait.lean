-- Prove2me | solution 1 for Csg.jointExpect_hide_wait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:25:39.920675+00:00
-- url     : https://prove2.me/submissions/8182b26e-9427-4c0f-9358-43119a9c62e8

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
import Theorems.Thm_Csg_skirmishState_sum

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .wait s').toReal * v s' = v .hide := by
  simp [jointK, skirmishState_sum, PMF.pure_apply]
end Csg
