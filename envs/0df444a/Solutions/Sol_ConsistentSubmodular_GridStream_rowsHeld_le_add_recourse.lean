-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.rowsHeld_le_add_recourse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:43.368049+00:00
-- url     : https://prove2.me/submissions/6d930937-e594-4457-b1a9-0d333dd7c1e2

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem solution (k : ℕ) {N : ℕ} (A B : Finset (Fin N)) :
    rowsHeld k B ≤ rowsHeld k A + recourse A B := by
  classical
  unfold rowsHeld recourse
  have hsub : B.filter (fun e => e.val < k) ⊆ A.filter (fun e => e.val < k) ∪ (B \ A) := by
    intro e he
    obtain ⟨heB, hek⟩ := mem_filter.mp he
    by_cases heA : e ∈ A
    · exact mem_union_left _ (mem_filter.mpr ⟨heA, hek⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨heB, heA⟩)
  calc (B.filter fun e => e.val < k).card
      ≤ ((A.filter fun e => e.val < k) ∪ (B \ A)).card := card_le_card hsub
    _ ≤ (A.filter fun e => e.val < k).card + (B \ A).card := card_union_le _ _
    _ ≤ (A.filter fun e => e.val < k).card + ((A \ B) ∪ (B \ A)).card := by
        gcongr
        exact subset_union_right

end
