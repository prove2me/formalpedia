-- Prove2me | solution 1 for BKAR.bkar_formula_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:31.854868+00:00
-- url     : https://prove2.me/submissions/d7b23e62-cbc9-48d6-a575-4581d4d069f4

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
import Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff

section
noncomputable section
namespace BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
private theorem bkar_formula_nonempty_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) :=
  BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
    hρ choices
end BKAR
end
end

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR
theorem _root_.solution
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        ρ zeroConfig +
          Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => I.edges ≠ ∅))
            (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
              (fun order =>
                Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                  [] [] 1 I order ρ)) :=
  fun choices => bkar_formula_nonempty_with_choices choices ρ hρ
end BKAR
