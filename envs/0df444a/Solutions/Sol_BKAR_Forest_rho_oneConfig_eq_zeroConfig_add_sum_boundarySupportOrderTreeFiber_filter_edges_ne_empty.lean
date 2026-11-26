-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:01.162995+00:00
-- url     : https://prove2.me/submissions/98dd1950-295a-4f9c-bc8c-9344d76b622d

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  rw [rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
    choices ρ hanalytic hfiber]
  rw [sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty]
end BKAR.Forest
