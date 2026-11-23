-- Prove2me | solution 1 for Csg.skirmishK_wet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:50.683368+00:00
-- url     : https://prove2.me/submissions/caec841e-d5e6-4089-9c4c-a6e33a7e96fa

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 : SoldierMove) (a2 : SniperMove) :
    skirmishCSG.K .wet a1 a2 = PMF.pure .wet := rfl
end Csg
