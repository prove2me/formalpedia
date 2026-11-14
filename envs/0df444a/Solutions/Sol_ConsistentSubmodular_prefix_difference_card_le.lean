-- Prove2me | solution 1 for ConsistentSubmodular.prefix_difference_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:08.786209+00:00
-- url     : https://prove2.me/submissions/a45e54f8-892d-43ea-b685-68073168da96

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SchedulingBasics

section

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem solution (s t : ℕ) :
    (arrivedPrefix n t \ arrivedPrefix n s).card ≤ t - s := by
  have hle : (arrivedPrefix n t \ arrivedPrefix n s).card ≤
      (Finset.range (t - s)).card := by
    refine Finset.card_le_card_of_injOn (fun e : Fin n => e.val - s) ?_ ?_
    · intro e he
      change e ∈ arrivedPrefix n t \ arrivedPrefix n s at he
      change e.val - s ∈ Finset.range (t - s)
      simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he
      simp only [Finset.mem_range]
      omega
    · intro e he e' he' heq
      change e ∈ arrivedPrefix n t \ arrivedPrefix n s at he
      change e' ∈ arrivedPrefix n t \ arrivedPrefix n s at he'
      simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he he'
      change e.val - s = e'.val - s at heq
      apply Fin.ext
      omega
  simpa using hle

end
