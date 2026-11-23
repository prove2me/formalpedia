-- Prove2me | solution 1 for Csg.penniesCSG_bwInd_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:46.506804+00:00
-- url     : https://prove2.me/submissions/7fe4ff21-bf67-449f-9a24-8925b186bd47

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_penniesCSG_stageValue_zero
import Theorems.Thm_Csg_CSG_bwInd_succ
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : penniesCSG.bwInd (0 : Unit → ℝ) 1 () = 0 := by
  rw [CSG.bwInd_succ, CSG.bwInd_zero]
  exact penniesCSG_stageValue_zero
end Csg
