-- Prove2me | solution 1 for Csg.jointExpect_run_wait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:12.088274+00:00
-- url     : https://prove2.me/submissions/225bbb4d-1be1-4beb-8221-8252c22c7f89

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
import Theorems.Thm_Csg_skirmishState_sum

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .wait s').toReal * v s' = v .home := by
  simp [jointK, skirmishState_sum, PMF.pure_apply]
end Csg
