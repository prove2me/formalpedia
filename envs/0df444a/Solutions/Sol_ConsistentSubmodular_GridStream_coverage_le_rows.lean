-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.coverage_le_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:18.342455+00:00
-- url     : https://prove2.me/submissions/3f5e015d-e0fa-4c48-893d-63118c0d9591

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage
import Theorems.Thm_ConsistentSubmodular_GridStream_card_cover_le

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem solution {k m : ℕ} (S : Finset (Fin (k + m * k)))
    (hS : S ⊆ arrivedPrefix (k + m * k) k) :
    coverageValue (gridStreamCover k m) S ≤ (rowsHeld k S : ℝ) * k := by
  have hcol : columnsHeld k S = 0 := by
    unfold columnsHeld
    rw [card_eq_zero, filter_eq_empty_iff]
    intro e he
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    omega
  have h := card_cover_le (m := m) S 0 (fun e he hke => by
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    omega)
  rw [hcol] at h
  unfold coverageValue
  have hc := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hc
  simpa using hc

end
