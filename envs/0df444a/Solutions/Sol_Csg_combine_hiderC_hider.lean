-- Prove2me | solution 1 for Csg.combine_hiderC_hider
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:24.411796+00:00
-- url     : https://prove2.me/submissions/9d1d289f-b7ec-4e60-8078-d8dde446f759

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (aC : NCSG.CoalitionAction SkirmishAction hiderC)
    (aC' : NCSG.ComplementAction SkirmishAction hiderC) :
    NCSG.combine hiderC aC aC' SkirmishPlayer.hider = hiderSingletonEquiv aC := rfl
end Csg
