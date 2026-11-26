-- Prove2me | solution 1 for BKAR.Forest.firstBoundarySupportContribution_eq_sum_supportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:43.434752+00:00
-- url     : https://prove2.me/submissions/7a2d30d5-42bd-4ea6-aadd-eb56bc3dcbde

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
import Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_def
import Theorems.Thm_BKAR_Forest_firstBoundarySupportOrderContribution_def
import Theorems.Thm_BKAR_ForestIndex_ext


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          firstBoundarySupportOrderContribution choices I order ρ) := by
  classical
  rw [firstBoundarySupportContribution_def choices I ρ]
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I),
        [e.val] ∈ edgeSetOrders I.edges := by
    intro e he
    exact
      activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
        (choices (Forest.empty V) e) (Finset.mem_filter.mp he).2
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach.filter
        (fun e => (choices (Forest.empty V) e).forest.support = I))
      (t := edgeSetOrders I.edges)
      (g := fun e => [e.val])
      hmap
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro order _
  rw [firstBoundarySupportOrderContribution_def choices I order ρ]
  have hfilter :
      ((Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I)).filter
          (fun e => [e.val] = order) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support = I ∧
              [e.val] = order) := by
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
end BKAR.Forest
