-- Prove2me | solution 1 for FairSelling.bagfill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:22.794922+00:00
-- url     : https://prove2.me/submissions/f7f63b65-b659-4086-98b1-f9e07121049c

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (u : G → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ S : Finset G, (∀ g ∈ S, u g ≤ hi - lo) → lo ≤ ∑ g ∈ S, u g →
      ∃ B ⊆ S, lo ≤ ∑ g ∈ B, u g ∧ ∑ g ∈ B, u g ≤ hi := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro _ hsum
    refine ⟨∅, Finset.Subset.refl _, by simpa using hsum, ?_⟩
    simp only [Finset.sum_empty]; linarith
  | @insert g S' hg IH =>
    intro hbound hsum
    by_cases hcase : lo ≤ ∑ x ∈ S', u x
    · obtain ⟨B, hB, hB1, hB2⟩ :=
        IH (fun x hx => hbound x (Finset.mem_insert_of_mem hx)) hcase
      exact ⟨B, hB.trans (Finset.subset_insert _ _), hB1, hB2⟩
    · push_neg at hcase
      refine ⟨insert g S', Finset.Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert hg]
      have hug : u g ≤ hi - lo := hbound g (Finset.mem_insert_self _ _)
      linarith
end FairSelling
