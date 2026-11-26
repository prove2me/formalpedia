-- Prove2me | solution 1 for BKAR.BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:01.343517+00:00
-- url     : https://prove2.me/submissions/480017b2-ecf4-4949-ba59-951038891c1e

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_empty_of_contDiff
import Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff_of_allBranchesAnalytic


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) :=
  hρ.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff_of_allBranchesAnalytic
    choices (hρ.allBranchesAnalytic_empty_of_contDiff choices)
end BKAR.BKARContDiff
