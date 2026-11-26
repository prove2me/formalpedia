-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.one_lt_growth_support_edges_card_iff_tail_order_ne_nil_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:11.264868+00:00
-- url     : https://prove2.me/submissions/86dd3dc8-b816-47fe-bf9a-590962e0943a

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
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
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    1 < (data.growth e).support.edges.card ↔
      (data.tail e).order ≠ [] := by
  constructor
  · intro hcard
    exact data.tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
      e rfl hcard
  · intro htail
    exact
      data.one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
        e htail
end BKAR.Forest.ActiveTerminalBranchData
