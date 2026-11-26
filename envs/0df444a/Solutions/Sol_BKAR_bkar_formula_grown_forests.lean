-- Prove2me | solution 1 for BKAR.bkar_formula_grown_forests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:10.715802+00:00
-- url     : https://prove2.me/submissions/6175052b-0613-40c6-a044-47cb86a7d226

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
import Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder

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
private theorem bkar_formula_grown_forests_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
          (fun order =>
            (Forest.grownForestForSupportOrder choices I order).orderedContribution
              order.val ρ)) := by
  rw [bkar_formula_with_choices choices ρ hρ]
  apply Finset.sum_congr rfl
  intro I _
  exact
    Forest.sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
      choices I ρ
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
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
            (fun order =>
              (Forest.grownForestForSupportOrder choices I order).orderedContribution
                order.val ρ)) :=
  fun choices => bkar_formula_grown_forests_with_choices choices ρ hρ
end BKAR
