-- Prove2me | solution 1 for Csg.skirmishK_hide_hide_throw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:07.105786+00:00
-- url     : https://prove2.me/submissions/ad1f73d1-0829-47e1-abcf-d6d5a409577d

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : skirmishCSG.K .hide .hide .throw = PMF.pure .home := rfl
end Csg
