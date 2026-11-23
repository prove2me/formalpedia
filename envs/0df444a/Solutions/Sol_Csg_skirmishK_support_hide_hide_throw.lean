-- Prove2me | solution 1 for Csg.skirmishK_support_hide_hide_throw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:48.63168+00:00
-- url     : https://prove2.me/submissions/4a767581-40a8-419b-9eb3-b961f43cbfae

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
import Theorems.Thm_Csg_skirmishK_hide_hide_throw

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (skirmishCSG.K .hide .hide .throw).support = {SkirmishPos.home} := by
  rw [skirmishK_hide_hide_throw]; exact PMF.support_pure _
end Csg
