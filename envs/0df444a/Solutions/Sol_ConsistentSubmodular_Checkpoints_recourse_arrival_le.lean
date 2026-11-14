-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.recourse_arrival_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:20.522828+00:00
-- url     : https://prove2.me/submissions/27e17d02-cfc5-4b35-8404-30e512a44a45

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem solution (B : Finset (Fin n)) (t : ℕ) :
    recourse (B ∩ arrivedPrefix n (t + 1)) (B ∩ arrivedPrefix n t) ≤ 1 := by
  unfold recourse
  have hsub : ((B ∩ arrivedPrefix n (t + 1)) \ (B ∩ arrivedPrefix n t)) ∪
      ((B ∩ arrivedPrefix n t) \ (B ∩ arrivedPrefix n (t + 1))) ⊆
      Finset.univ.filter (fun e : Fin n => e.val = t) := by
    intro x hx
    simp only [arrivedPrefix, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨⟨hb, h1⟩, h2⟩ | ⟨⟨hb, h1⟩, h2⟩
    · have h3 : ¬ x.val < t := fun h => h2 ⟨hb, h⟩
      omega
    · exact absurd ⟨hb, by omega⟩ h2
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact Fin.ext (ha.trans hb.symm)

end
