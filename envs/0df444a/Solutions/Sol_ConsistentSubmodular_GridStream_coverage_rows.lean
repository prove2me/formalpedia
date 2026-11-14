-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.coverage_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:44.5422+00:00
-- url     : https://prove2.me/submissions/52abdab5-0f09-4732-b154-1bca3a62c2fe

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem solution {k m : ℕ} :
    (k : ℝ) * k ≤ coverageValue (gridStreamCover k m) (arrivedPrefix (k + m * k) k) := by
  classical
  unfold coverageValue
  have hsub : range (k * k) ⊆
      ((arrivedPrefix (k + m * k) k).biUnion (gridStreamCover k m)).map Fin.valEmbedding := by
    intro y hy
    have hy' : y < k * k := mem_range.mp hy
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at hy'
      · exact h
    have hr : y / k < k := (Nat.div_lt_iff_lt_mul hk).mpr hy'
    refine mem_map.mpr ⟨⟨y, by omega⟩, mem_biUnion.mpr ⟨⟨y / k, by omega⟩, ?_, ?_⟩, rfl⟩
    · simp [arrivedPrefix, hr]
    · simp [gridStreamCover, hr, hy']
  have := card_le_card hsub
  rw [card_range, card_map] at this
  exact_mod_cast this

end
