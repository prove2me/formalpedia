-- Prove2me | solution 1 for Csg.skirmishK_support_hide_hide_wait
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:41.864393+00:00
-- url     : https://prove2.me/submissions/1f549982-ef9f-4bc3-a3a9-10cd7215d6fd

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
import Theorems.Thm_Csg_skirmishK_hide_hide_wait

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (skirmishCSG.K .hide .hide .wait).support = {SkirmishPos.hide} := by
  rw [skirmishK_hide_hide_wait]; exact PMF.support_pure _
end Csg
