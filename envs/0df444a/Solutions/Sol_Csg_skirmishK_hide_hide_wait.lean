-- Prove2me | solution 1 for Csg.skirmishK_hide_hide_wait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:01.925889+00:00
-- url     : https://prove2.me/submissions/663590c6-62b9-48db-88a6-92082a701941

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : skirmishCSG.K .hide .hide .wait = PMF.pure .hide := rfl
end Csg
