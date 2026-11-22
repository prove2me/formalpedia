-- Prove2me | solution 1 for Csg.outcome_col_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:14:16.426884+00:00
-- url     : https://prove2.me/submissions/492a0760-11ce-45f0-8920-394a0b882377

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a2 : RPSAction) (v : RPSState → ℝ) :
    v (outcome .rock a2) + v (outcome .paper a2) + v (outcome .scissors a2) =
      v .win1 + v .win2 + v .draw := by
  cases a2 <;> simp only [outcome] <;> ring
end Csg
