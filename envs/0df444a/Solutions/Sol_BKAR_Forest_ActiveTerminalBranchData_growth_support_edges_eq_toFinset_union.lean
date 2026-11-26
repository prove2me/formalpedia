-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_support_edges_eq_toFinset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:51.818013+00:00
-- url     : https://prove2.me/submissions/55faf9f3-5b6d-48a1-934b-bf978bb17414

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_union
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges_eq_toFinset_union
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).support.edges =
      (e.val :: (data.tail e).order).toFinset ∪ F.edges :=
  (data.growth e).support_edges_eq_toFinset_union
end BKAR.Forest.ActiveTerminalBranchData
