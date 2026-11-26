-- Prove2me | solution 1 for BKAR.bkar_formula_canonical_grown_cube_contributions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:27.588621+00:00
-- url     : https://prove2.me/submissions/8bb5d5d7-8fb1-42c9-ae80-62dc2a6debc5

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
import Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
import Theorems.Thm_BKAR_Forest_sum_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonicalGrownForestForSupport_cubeContribution
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
private theorem bkar_formula_grown_forest_cube_sectors_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
          (fun order =>
            (Forest.grownForestForSupportOrder choices I order).orderedCubeSectorContribution
              order.val ρ)) := by
  rw [bkar_formula_grown_forests_with_choices choices ρ hρ]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro order _
  exact
    Forest.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
      (Forest.grownForestForSupportOrder choices I order)
      (Forest.grownForestForSupportOrder_order_mem_edgeOrders choices I order)
      ρ hρ
private theorem bkar_formula_canonical_grown_cube_contributions_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig = canonicalGrownForestCubeContributionSum choices ρ := by
  rw [bkar_formula_grown_forest_cube_sectors_with_choices choices ρ hρ]
  rw [canonicalGrownForestCubeContributionSum]
  apply Finset.sum_congr rfl
  intro I _hI
  exact
    Forest.sum_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonicalGrownForestForSupport_cubeContribution
      choices I ρ hρ
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
      ρ oneConfig = canonicalGrownForestCubeContributionSum choices ρ :=
  fun choices =>
    bkar_formula_canonical_grown_cube_contributions_with_choices
      choices ρ hρ
end BKAR
