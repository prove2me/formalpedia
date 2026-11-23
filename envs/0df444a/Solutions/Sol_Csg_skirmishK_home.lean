-- Prove2me | solution 1 for Csg.skirmishK_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:53.448078+00:00
-- url     : https://prove2.me/submissions/4c0d6311-f5a6-4775-bb17-00b74df8b5af

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 : SoldierMove) (a2 : SniperMove) :
    skirmishCSG.K .home a1 a2 = PMF.pure .hide := rfl
end Csg
