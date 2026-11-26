-- Prove2me | solution 1 for BKAR.Forest.sum_integral_allBranchesBoundaryExpansion_child_eq_sum_localBoundarySupportOrderContribution_add_sum_integral_child_sum_of_allBranchesAnalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:00.58864+00:00
-- url     : https://prove2.me/submissions/aa52b15b-d8b2-483a-abba-248df305916d

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_sum_localBoundarySupportOrderContribution
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum_of_allBranchesAnalytic
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          allBranchesBoundaryExpansion choices
            (choices F e).forest.activeEdges.card
            (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices (choices F e).forest e').forest.activeEdges.card
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
  have hsplit :
      Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) =
        Finset.sum F.activeEdges.attach
          (fun e =>
            orderedSimplexIntegralAux top [e.val]
              (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
                ((choices F e).forest.standardInterp
                  ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                    (prefixTs ++ ts)))) +
            ∫ t in 0..top,
              Finset.sum (choices F e).forest.activeEdges.attach
                (fun e' => ∫ s in 0..t,
                  allBranchesBoundaryExpansion choices
                    (choices (choices F e).forest e').forest.activeEdges.card
                    (choices (choices F e).forest e').forest
                    ((pref ++ [e.val]) ++ [e'.val])
                    ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
    apply Finset.sum_congr rfl
    intro e _
    exact
      integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum_of_allBranchesAnalytic
        choices F e pref prefixTs top ρ hanalytic
  rw [hsplit]
  rw [Finset.sum_add_distrib]
  rw [sum_localBoundarySupportOrderContribution choices F pref prefixTs top
    hpref hnodup ρ]
end BKAR.Forest
