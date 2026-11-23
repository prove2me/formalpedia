-- Prove2me | solution 1 for Csg.skirmishK_support_hide_run_throw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:25.237794+00:00
-- url     : https://prove2.me/submissions/2a3e2eb4-df2e-4999-819a-c5e0dbeaf53a

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
import Theorems.Thm_Csg_skirmishK_hide_run_throw

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (skirmishCSG.K .hide .run .throw).support = {SkirmishPos.wet} := by
  rw [skirmishK_hide_run_throw]; exact PMF.support_pure _
end Csg
