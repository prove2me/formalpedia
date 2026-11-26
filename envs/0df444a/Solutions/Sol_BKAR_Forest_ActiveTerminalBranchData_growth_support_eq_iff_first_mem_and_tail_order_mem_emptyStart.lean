-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:54.30012+00:00
-- url     : https://prove2.me/submissions/5b32f0b5-2714-4b7f-b38f-20bd5f0b1d3b

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_order_toFinset_eq_emptyStart
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_nodup
import Theorems.Thm_BKAR_Forest_cons_mem_edgeSetOrders_iff
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff_toFinset_eq_and_nodup
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders
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
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (I : ForestIndex V) :
    (data.growth e).support = I ↔
      e.val ∈ I.edges ∧
        (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val) := by
  constructor
  · intro hsupport
    have horder :
        e.val :: (data.tail e).order ∈ edgeSetOrders I.edges := by
      rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
      exact ⟨
        (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I).mp
          hsupport,
        data.growth_order_nodup e⟩
    exact
      (cons_mem_edgeSetOrders_iff I.edges).mp
        horder
  · intro h
    apply
      (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I).mpr
    have htail :
        (data.tail e).order.toFinset = I.edges.erase e.val :=
      toFinset_eq_of_mem_edgeSetOrders h.2
    rw [List.toFinset_cons, htail, Finset.insert_erase h.1]
end BKAR.Forest.ActiveTerminalBranchData
