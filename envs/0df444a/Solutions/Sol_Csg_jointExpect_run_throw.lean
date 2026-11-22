-- Prove2me | solution 1 for Csg.jointExpect_run_throw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:20.191709+00:00
-- url     : https://prove2.me/submissions/ead353ad-ec63-4ac5-897b-5041c5c754a2

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
import Theorems.Thm_Csg_skirmishState_sum

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .throw s').toReal * v s' = v .wet := by
  simp [jointK, skirmishState_sum, PMF.pure_apply]
end Csg
