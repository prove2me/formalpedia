-- Prove2me | solution 1 for Csg.skirmishK_hide_run_wait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:40.956624+00:00
-- url     : https://prove2.me/submissions/7b06d2c1-cfa4-479b-ae0f-820cfa1e8131

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : skirmishCSG.K .hide .run .wait = PMF.pure .home := rfl
end Csg
