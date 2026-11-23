-- Prove2me | solution 1 for Csg.rpsCSGSteps_rewardUntilOp_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:47.211813+00:00
-- url     : https://prove2.me/submissions/4cc8fc4f-bac1-45d0-8a28-ec65b37bd0a4

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsSteps_fixed
import Theorems.Thm_Csg_rpsSteps_unique
import Theorems.Thm_Csg_CSG_rewardUntilOp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    ∃! w : RPSState → ℝ,
      rpsCSGSteps.rewardUntilStep (fun s => s = RPSState.win1 ∨ s = RPSState.win2) w = w :=
  rpsCSGSteps.rewardUntilOp_eq_of_certificate (fun s => s = RPSState.win1 ∨ s = RPSState.win2)
    rpsSteps rpsSteps_fixed fun _w hw => rpsSteps_unique hw
end Csg
