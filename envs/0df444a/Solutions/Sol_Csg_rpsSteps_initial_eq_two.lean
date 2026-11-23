-- Prove2me | solution 1 for Csg.rpsSteps_initial_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:51.378434+00:00
-- url     : https://prove2.me/submissions/6c97f909-403f-4212-80fd-b9bb659c12cd

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsSteps RPSState.initial = 2 := rfl
end Csg
