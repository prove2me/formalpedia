-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_derivativeOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:35.280861+00:00
-- url     : https://prove2.me/submissions/9946384f-8f1d-47fb-88e9-13d3049b67ee

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
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
    ((data.growth e).growth).derivativeOrder =
      (e.val :: (data.tail e).order).reverse :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
