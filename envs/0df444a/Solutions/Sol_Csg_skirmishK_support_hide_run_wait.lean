-- Prove2me | solution 1 for Csg.skirmishK_support_hide_run_wait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:07:54.265095+00:00
-- url     : https://prove2.me/submissions/0d2feef3-0706-42f6-ba70-0cd6eee5254b

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
import Theorems.Thm_Csg_skirmishK_hide_run_wait

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (skirmishCSG.K .hide .run .wait).support = {SkirmishPos.home} := by
  rw [skirmishK_hide_run_wait]; exact PMF.support_pure _
end Csg
