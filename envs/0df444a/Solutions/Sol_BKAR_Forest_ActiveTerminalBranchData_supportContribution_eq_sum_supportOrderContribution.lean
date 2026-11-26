-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_supportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:14.031721+00:00
-- url     : https://prove2.me/submissions/c7dc9f88-9f7a-4b79-9ba2-35c6f4dcf24c

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_def
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_def
import Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
import Theorems.Thm_BKAR_ForestIndex_ext


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
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order => data.supportOrderContribution I order ρ) := by
  classical
  rw [data.supportContribution_def I ρ]
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I),
        data.growthOrder e ∈ edgeSetOrders I.edges := by
    intro e he
    exact data.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart e
      (Finset.mem_filter.mp he).2
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach.filter
        (fun e => (data.growth e).support = I))
      (t := edgeSetOrders I.edges)
      (g := fun e => data.growthOrder e)
      hmap
      (fun e => (data.growth e).terminal.orderedContribution
        (data.growthOrder e) ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro order _
  rw [data.supportOrderContribution_def I order ρ]
  have hfilter :
      ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I)).filter
          (fun e => data.growthOrder e = order) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I ∧
            data.growthOrder e = order) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_filter.mp he).2.2]
end BKAR.Forest.ActiveTerminalBranchData
