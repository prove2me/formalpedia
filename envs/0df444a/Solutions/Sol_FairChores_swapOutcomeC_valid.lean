-- Prove2me | solution 1 for FairChores.swapOutcomeC_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:45.078951+00:00
-- url     : https://prove2.me/submissions/fceb73e5-0d98-4189-a1b6-1995811245c0

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (p : T → ℝ) (o : Outcome T 2) (h : o.Valid p) :
    (swapOutcomeC o).Valid p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun i => h1 _, fun i j hij => h2 _ _ (fun he => hij ((Equiv.swap 0 1).injective he)),
    ?_, fun i => h4 _, ?_⟩
  · show o.outsourced ∪ Finset.univ.biUnion (fun i => o.kept (Equiv.swap 0 1 i)) = Finset.univ
    rw [← h3]
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨Equiv.swap 0 1 i, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨Equiv.swap 0 1 i, by simpa using hi⟩
  · show _ ≤ ∑ i, o.pay (Equiv.swap 0 1 i)
    rw [Equiv.sum_comp (Equiv.swap 0 1) o.pay]; exact h5
end FairChores
