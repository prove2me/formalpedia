-- Prove2me | solution 1 for BKAR.BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff_of_allBranchesAnalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:28.266255+00:00
-- url     : https://prove2.me/submissions/fc72ebc7-b0e0-4bed-976a-b9e23ac84ff4

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_nontrivialIntegrable


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (hanalytic :
      Forest.allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) :=
  Forest.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_nontrivialIntegrable
    choices ρ hanalytic
    (hρ.boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
      choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 rfl)
end BKAR.BKARContDiff
