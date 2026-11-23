-- Prove2me | solution 1 for Csg.skirmishK_hide_run_throw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:07:44.806267+00:00
-- url     : https://prove2.me/submissions/552d5109-ae61-4e3c-8850-828054e32a35

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : skirmishCSG.K .hide .run .throw = PMF.pure .wet := rfl
end Csg
