-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:48.440172+00:00
-- url     : https://prove2.me/submissions/a7f479b5-941b-4d8a-ab8e-b371c5a48ac8

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_ForestIndex_singleton_edges
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_singleton_eq_orderedContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I [a]) =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by
  classical
  rw [Finset.sum_eq_single_of_mem (ForestIndex.singleton a)
    (Finset.mem_univ (ForestIndex.singleton a))]
  · exact rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
      choices a ρ
  · intro I _ hne
    exact
      rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
        choices a ρ I (by
          intro hIedges
          apply hne
          apply ForestIndex.ext
          rw [hIedges, ForestIndex.singleton_edges])
end BKAR.Forest
