-- Prove2me | solution 1 for C6BipartiteDomination.wb_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:07.621844+00:00
-- url     : https://prove2.me/submissions/99f3f5c9-6fbd-437a-a751-3c52cce15558

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_PPart_subset_WBPart
import Theorems.Thm_C6BipartiteDomination_card_PPart
import Theorems.Thm_C6BipartiteDomination_private_card_eq_two_add_x

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D) :
    (WBPart G D).card =
      2 * (BPart G D).card +
        (∑ b ∈ BPart G D, xCharge G D b) + (SPart G D).card := by
  classical
  have hPsub : PPart G D ⊆ WBPart G D := PPart_subset_WBPart G D
  have hUnion : PPart G D ∪ SPart G D = WBPart G D := by
    ext w
    simp only [Finset.mem_union, mem_SPart]
    constructor
    · rintro (hP | ⟨hWB, _⟩)
      · exact hPsub hP
      · exact hWB
    · intro hWB
      by_cases hP : w ∈ PPart G D
      · exact Or.inl hP
      · exact Or.inr ⟨hWB, hP⟩
  have hdisj : Disjoint (PPart G D) (SPart G D) := by
    rw [Finset.disjoint_left]
    intro w hwP hwS
    exact (mem_SPart G D w).mp hwS |>.2 hwP
  have hPcard := card_PPart G D
  have hsum :
      (∑ b ∈ BPart G D, (privateExternalNeighbors G D b).card) =
        2 * (BPart G D).card + ∑ b ∈ BPart G D, xCharge G D b := by
    calc
      _ = ∑ b ∈ BPart G D, (2 + xCharge G D b) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact private_card_eq_two_add_x G hCan hb
      _ = 2 * (BPart G D).card + ∑ b ∈ BPart G D, xCharge G D b := by
        simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
  rw [← hUnion, Finset.card_union_of_disjoint hdisj, hPcard, hsum]
end C6BipartiteDomination
