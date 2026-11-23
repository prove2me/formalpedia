-- Prove2me | solution 1 for Csg.rpsSteps_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:53:02.830049+00:00
-- url     : https://prove2.me/submissions/d13246e7-b31a-4969-ae4e-f181223bee36

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_stageValue_draw
import Theorems.Thm_Csg_rpsCSGSteps_stageValue_initial

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsStepsStep rpsSteps = rpsSteps := by
  funext s
  cases s with
  | win1 => rfl
  | win2 => rfl
  | initial =>
      change rpsCSGSteps.stageValue RPSState.initial rpsSteps = rpsSteps RPSState.initial
      rw [rpsCSGSteps_stageValue_initial]
      norm_num [rpsSteps]
  | draw =>
      change rpsCSGSteps.stageValue RPSState.draw rpsSteps = rpsSteps RPSState.draw
      rw [rpsCSGSteps_stageValue_draw]
      norm_num [rpsSteps]
end Csg
