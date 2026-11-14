-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.card_stageColumns
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:45.133195+00:00
-- url     : https://prove2.me/submissions/7cb85e1a-84b4-4c7a-9f2c-b77931c0ffad

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem solution {k m j : ℕ} (hj : j ≤ m) : (stageColumns k m j).card = k := by
  have hjm : j * k ≤ m * k := Nat.mul_le_mul_right k hj
  have hsucc : (j + 1) * k = j * k + k := Nat.succ_mul j k
  have hmap : (stageColumns k m j).map Fin.valEmbedding = Ico (j * k) ((j + 1) * k) := by
    ext x
    simp only [stageColumns, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, hmap, Nat.card_Ico]
  omega

end
