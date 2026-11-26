-- Prove2me | solution 1 for BKAR.Forest.sum_firstBoundarySupportContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:28.387797+00:00
-- url     : https://prove2.me/submissions/d8764ac7-66f0-48f8-8e6b-fae2530dee12

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_def

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Forest.empty V).activeEdges.attach
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => firstBoundarySupportContribution choices I ρ) := by
  classical
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach,
        (choices (Forest.empty V) e).forest.support ∈
          (Finset.univ : Finset (ForestIndex V)) := by
    intro e _
    exact Finset.mem_univ _
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach)
      (t := (Finset.univ : Finset (ForestIndex V)))
      (g := fun e => (choices (Forest.empty V) e).forest.support)
      hmap
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro I _
  rw [firstBoundarySupportContribution_def choices I ρ]
end BKAR.Forest
