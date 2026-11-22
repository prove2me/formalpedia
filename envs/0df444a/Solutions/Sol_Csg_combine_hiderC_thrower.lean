-- Prove2me | solution 1 for Csg.combine_hiderC_thrower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:27.654388+00:00
-- url     : https://prove2.me/submissions/4d06b05e-427f-4ada-a208-dbdae7b2f666

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (aC : NCSG.CoalitionAction SkirmishAction hiderC)
    (aC' : NCSG.ComplementAction SkirmishAction hiderC) :
    NCSG.combine hiderC aC aC' SkirmishPlayer.thrower = throwerComplementEquiv aC' := rfl
end Csg
