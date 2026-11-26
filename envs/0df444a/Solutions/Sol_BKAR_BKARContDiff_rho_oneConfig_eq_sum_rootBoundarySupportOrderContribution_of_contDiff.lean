-- Prove2me | solution 1 for BKAR.BKARContDiff.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:39.017419+00:00
-- url     : https://prove2.me/submissions/4be1dcc5-5f0e-45e6-859f-a8b34f7a984c

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty


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
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
          (fun order =>
            Forest.rootBoundarySupportOrderContribution choices ρ I order)) := by
  rw [Forest.sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty]
  exact
    hρ.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
      choices
end BKAR.BKARContDiff
