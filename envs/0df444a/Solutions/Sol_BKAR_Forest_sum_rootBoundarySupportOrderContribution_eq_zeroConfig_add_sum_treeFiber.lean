-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:03.065517+00:00
-- url     : https://prove2.me/submissions/355b6bbf-5132-4cc9-88ff-5b9e59069091

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_def
import Theorems.Thm_BKAR_Forest_sum_emptySupportOrderMarker

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) =
      ρ zeroConfig +
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  rw [show
      Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              rootBoundarySupportOrderContribution choices ρ I order)) =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I =>
            Finset.sum (edgeSetOrders I.edges)
              (fun order =>
                if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
            Finset.sum (edgeSetOrders I.edges)
              (fun order =>
                boundarySupportOrderTreeFiber choices (Forest.empty V) [] []
                  1 I order ρ)) by
    apply Finset.sum_congr rfl
    intro I _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro order _
    rw [rootBoundarySupportOrderContribution_def]]
  rw [Finset.sum_add_distrib]
  rw [sum_emptySupportOrderMarker]
end BKAR.Forest
