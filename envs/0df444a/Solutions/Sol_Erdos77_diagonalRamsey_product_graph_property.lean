-- Prove2me | solution 1 for Erdos77.diagonalRamsey_product_graph_property
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:17:26.919955+00:00
-- url     : https://prove2.me/submissions/200023a6-a025-49ab-862e-590481987daa

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

open Erdos77

lemma ramsey_one : diagonalRamsey 1 = 1 := by
  unfold diagonalRamsey
  let Q : Nat → Prop := fun n => ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique 1 s) ∨
    (∃ s : Finset (Fin n), (Compl.compl G).IsNClique 1 s)
  change sInf {n | Q n} = 1
  have hset : {n | Q n} = {n | Nonempty (Fin n)} := by
    ext n
    simp [Q, SimpleGraph.isNClique_one]
  rw [hset]
  let P : Set Nat := {n | Nonempty (Fin n)}
  have hup : ∀ a b : Nat, a ≤ b → a ∈ P → b ∈ P := by
    intro a b hab ha
    rcases ha with ⟨i⟩
    exact ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hab⟩⟩
  rw [Nat.sInf_upward_closed_eq_succ_iff hup 0]
  constructor
  · exact ⟨⟨0, by omega⟩⟩
  · intro h0
    rcases h0 with ⟨i⟩
    exact Nat.not_lt_zero _ i.isLt

theorem solution : ¬ (∀ m n : Nat, 0 < m → 0 < n →
    ∀ G : SimpleGraph (Fin (diagonalRamsey m * diagonalRamsey n)),
      (∃ s : Finset (Fin (diagonalRamsey m * diagonalRamsey n)), G.IsNClique (m + n) s) ∨
      (∃ s : Finset (Fin (diagonalRamsey m * diagonalRamsey n)),
        (Compl.compl G).IsNClique (m + n) s)) := by
  intro h
  have h11 := h 1 1 (by omega) (by omega)
  rw [ramsey_one] at h11
  let G : SimpleGraph (Fin (1 * 1)) := ⊥
  rcases h11 G with ⟨s, hs⟩ | ⟨s, hs⟩
  all_goals
    rw [SimpleGraph.isNClique_iff] at hs
    have hcard := Finset.card_le_card (Finset.subset_univ s)
    have : s.card ≤ 1 := by simpa using hcard
    omega