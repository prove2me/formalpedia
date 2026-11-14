-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.le_benchmark
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:22.611209+00:00
-- url     : https://prove2.me/submissions/e99ac3c1-732b-4999-889c-9bbcacb64bd6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointWindow

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem solution (f : Objective n) (κ c : ℕ) (j : Fin ((window f κ c).lastStage + 1))
    {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (c + j.val)) (hcard : T.card ≤ κ) :
    f.value T ≤ (window f κ c).benchmark j := by
  classical
  have hsplit : T ⊆ (T ∩ arrivedPrefix n c) ∪ future n c j.val := by
    intro e he
    have he' := hT he
    simp only [arrivedPrefix, future, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at he' ⊢
    by_cases hc : e.val < c
    · exact Or.inl ⟨he, hc⟩
    · exact Or.inr ⟨by omega, he'⟩
  have hmono := f.monotone _ _ hsplit
  have hopt := (window f κ c).candidate_optimal j (T ∩ arrivedPrefix n c)
    Finset.inter_subset_right ((Finset.card_le_card Finset.inter_subset_left).trans hcard)
  exact hmono.trans hopt

end
