-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:48.895749+00:00
-- url     : https://prove2.me/submissions/26d549b4-8bca-48df-a2f4-bf46a1e84cf8

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_integral_child_sum
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


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
    (hstd :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])))
          MeasureTheory.volume 0 1)
    (hrec :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
          MeasureTheory.volume 0 1) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_integral_child_sum
    choices ρ hanalytic hstd hrec]
  rw [Finset.sum_add_distrib]
end BKAR.Forest
