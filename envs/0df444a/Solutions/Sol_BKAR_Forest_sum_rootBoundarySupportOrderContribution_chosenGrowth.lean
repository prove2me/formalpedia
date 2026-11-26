-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_chosenGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:37.325376+00:00
-- url     : https://prove2.me/submissions/1951a164-af4e-4f69-8671-32ce267ddf02

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_nil
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_ChosenGrowth_support_edges_eq_toFinset_emptyStart
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_emptyStart
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      G.orderedContribution order ρ := by
  classical
  by_cases horder : order = []
  · subst order
    cases path with
    | nil F =>
        exact sum_rootBoundarySupportOrderContribution_nil choices ρ
  · have hsupport : order.toFinset = G.support.edges := by
      rw [ChosenGrowth.support_edges_eq_toFinset_emptyStart path]
    rw [Finset.sum_eq_single_of_mem G.support (Finset.mem_univ G.support)]
    · exact
        rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
          choices path ρ horder
    · intro I _ hne
      exact
        rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
          choices ρ I order (by
            intro hI
            apply hne
            apply ForestIndex.ext
            rw [← hI, hsupport])
end BKAR.Forest
