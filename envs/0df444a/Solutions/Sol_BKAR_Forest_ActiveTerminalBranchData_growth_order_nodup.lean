-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_order_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:18.344591+00:00
-- url     : https://prove2.me/submissions/e3d9509b-4182-4012-a13e-3da498700e7a

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_nodup
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (e.val :: (data.tail e).order).Nodup :=
  (data.growth e).order_nodup
end BKAR.Forest.ActiveTerminalBranchData
