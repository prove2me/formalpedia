-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:02.352738+00:00
-- url     : https://prove2.me/submissions/2e64888c-4249-45f8-8df9-503cf99889cc

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I []) =
      (Forest.empty V).orderedContribution [] ρ := by
  classical
  let I0 : ForestIndex V := (Forest.empty V).support
  have hI0edges : I0.edges = ∅ := rfl
  rw [Finset.sum_eq_single_of_mem I0 (Finset.mem_univ I0)]
  · exact
      rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
        choices ρ I0 hI0edges
  · intro I _ hne
    have hIedges : I.edges ≠ ∅ := by
      intro hempty
      apply hne
      apply ForestIndex.ext
      rw [hempty, hI0edges]
    exact
      rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
        choices ρ I hIedges
end BKAR.Forest
