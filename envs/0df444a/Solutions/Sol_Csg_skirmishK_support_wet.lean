-- Prove2me | solution 1 for Csg.skirmishK_support_wet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:10.06783+00:00
-- url     : https://prove2.me/submissions/74329437-b140-4e04-a586-4fd81b299e25

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
import Theorems.Thm_Csg_skirmishK_wet

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 : SoldierMove) (a2 : SniperMove) :
    (skirmishCSG.K .wet a1 a2).support = {SkirmishPos.wet} := by
  rw [skirmishK_wet]; exact PMF.support_pure _
end Csg
