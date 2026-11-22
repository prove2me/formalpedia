-- Prove2me | solution 1 for Csg.unif3_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:14:48.1088+00:00
-- url     : https://prove2.me/submissions/db59b32d-8e36-43b2-ac01-24313e6f711e

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsAction_sum
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : unif3 ∈ stdSimplex ℝ RPSAction :=
  ⟨fun a => by simp only [unif3]; norm_num, by simp only [unif3, rpsAction_sum]; norm_num⟩
end Csg
