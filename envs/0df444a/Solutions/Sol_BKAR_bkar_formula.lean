-- Prove2me | solution 1 for BKAR.bkar_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:05.267803+00:00
-- url     : https://prove2.me/submissions/0c575e1d-4f73-4b03-9fff-85f6e1e2970a

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
import Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff

section
noncomputable section
namespace BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
private theorem bkar_formula_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
          (fun order =>
            Forest.rootBoundarySupportOrderContribution choices ρ I order)) :=
  BKARContDiff.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
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
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.rootBoundarySupportOrderContribution choices ρ I order)) :=
  fun choices => bkar_formula_with_choices choices ρ hρ
end BKAR
