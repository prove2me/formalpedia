-- Prove2me | solution 1 for Csg.skirmishK_support_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:34.779788+00:00
-- url     : https://prove2.me/submissions/9490d906-6bc8-4969-b5cc-7bb59689b840

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
import Theorems.Thm_Csg_skirmishK_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 : SoldierMove) (a2 : SniperMove) :
    (skirmishCSG.K .home a1 a2).support = {SkirmishPos.hide} := by
  rw [skirmishK_home]; exact PMF.support_pure _
end Csg
