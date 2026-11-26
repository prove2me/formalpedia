-- Prove2me | solution 1 for C6BipartiteDomination.outside_partition_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:17.272579+00:00
-- url     : https://prove2.me/submissions/ee7948bd-f510-4761-9e97-998740eb3961

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_mem_WBPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    (Finset.univ \ D).card = (W0Part G D).card + (WBPart G D).card := by
  classical
  have hdisj : Disjoint (W0Part G D) (WBPart G D) := by
    rw [Finset.disjoint_left]
    intro v hv0 hvb
    exact ((mem_WBPart G D v).mp hvb).2 hv0
  have hunion : W0Part G D ∪ WBPart G D = Finset.univ \ D := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (hv0 | hvb)
      · exact (mem_W0Part G D v).mp hv0 |>.1
      · exact (mem_WBPart G D v).mp hvb |>.1
    · intro hvD
      by_cases hv0 : v ∈ W0Part G D
      · exact Or.inl hv0
      · exact Or.inr ((mem_WBPart G D v).mpr ⟨hvD, hv0⟩)
  calc
    (Finset.univ \ D).card = (W0Part G D ∪ WBPart G D).card := by
      rw [hunion]
    _ = (W0Part G D).card + (WBPart G D).card :=
      Finset.card_union_of_disjoint hdisj
end C6BipartiteDomination
