-- Prove2me | solution 1 for Csg.rpsSteps_draw_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:42:20.798552+00:00
-- url     : https://prove2.me/submissions/3a116b98-f6cd-4bf9-8c81-59b0f4c76c75

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsSteps RPSState.draw = 3 := rfl
end Csg
