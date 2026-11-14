-- Prove2me | solution 1 for ConsistentSubmodular.gridStreamCrossing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:22.518429+00:00
-- url     : https://prove2.me/submissions/aeeed5fc-0139-4bcd-9d22-2cd776c25d57

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_le_rows
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_rows
import Theorems.Thm_ConsistentSubmodular_GridStream_rows_after_stage

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

theorem card_arrivedPrefix {n t : ℕ} (h : t ≤ n) : (arrivedPrefix n t).card = t := by
  have hmap : (arrivedPrefix n t).map Fin.valEmbedding = range t := by
    ext x
    simp only [arrivedPrefix, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, hmap, card_range]

end ConsistentSubmodular.GridStream

end

end

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

section Lemma6

variable {k m C : ℕ} {S : Fin (k + m * k + 1) → Finset (Fin (k + m * k))}

/-- Part 1 of Lemma 6: once the rows have arrived, the comparison with all rows
forces `n_k ≥ 3k/4`. -/
theorem rows_at_k (hk : 0 < k) (hS : FeasibleTrajectory k C S)
    (happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t)) :
    3 * k ≤ 4 * rowsHeld k (S ⟨k, by omega⟩) := by
  set t₀ : Fin (k + m * k + 1) := ⟨k, by omega⟩
  have hA := happrox t₀ (arrivedPrefix (k + m * k) k) subset_rfl
    (card_arrivedPrefix (by omega)).le
  have hrows := coverage_rows (k := k) (m := m)
  have hS0 := coverage_le_rows (S t₀) (hS.2.1 t₀).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h : (3 * (k : ℝ)) * k ≤ (4 * (rowsHeld k (S t₀) : ℝ)) * k := by nlinarith
  exact_mod_cast le_of_mul_le_mul_right h hkR

end Lemma6

/-- **Lemma 6** (behavior on the stream `Σ`): part 1 at time `k`, part 2 at the
end of stage `k`, time `k (k + 1) > k`. -/
theorem gridStreamCrossing : GridStreamCrossingGoal := by
  intro k m hk C S hS happrox
  refine ⟨rows_at_k hk hS happrox, fun hm => ?_⟩
  have hmk := Nat.mul_le_mul_right k hm
  exact ⟨⟨k + k * k, by omega⟩, Nat.lt_add_of_pos_right (Nat.mul_pos hk hk),
    rows_after_stage hk hm hS happrox⟩

end ConsistentSubmodular.GridStream

end

end

section

open ConsistentSubmodular

theorem solution : GridStreamCrossingGoal :=
  GridStream.gridStreamCrossing

end
