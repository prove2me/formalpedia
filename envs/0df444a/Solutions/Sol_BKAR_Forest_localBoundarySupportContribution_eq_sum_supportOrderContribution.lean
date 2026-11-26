-- Prove2me | solution 1 for BKAR.Forest.localBoundarySupportContribution_eq_sum_supportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:52.537637+00:00
-- url     : https://prove2.me/submissions/365bd42d-caec-448d-b0d0-4794c3e2d910

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
import Theorems.Thm_BKAR_Forest_localBoundarySupportContribution_def
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_ForestIndex_ext


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportContribution choices F pref prefixTs top I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ) := by
  classical
  rw [localBoundarySupportContribution_def choices F pref prefixTs top I ρ]
  have hmap :
      ∀ e ∈ F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I),
        pref ++ [e.val] ∈ edgeSetOrders I.edges := by
    intro e he
    exact
      activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
        (choices F e) hpref hnodup (Finset.mem_filter.mp he).2
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := F.activeEdges.attach.filter
        (fun e => (choices F e).forest.support = I))
      (t := edgeSetOrders I.edges)
      (g := fun e => pref ++ [e.val])
      hmap
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ ts)))))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro order _
  rw [localBoundarySupportOrderContribution_def choices F pref prefixTs top
    I order ρ]
  have hfilter :
      (F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I)).filter
          (fun e => pref ++ [e.val] = order) =
        F.activeEdges.attach.filter
          (fun e =>
            (choices F e).forest.support = I ∧
              pref ++ [e.val] = order) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_filter.mp he).2.2]
end BKAR.Forest
