-- Prove2me | solution 1 for ConsistentSubmodular.exists_two_labels_of_supportCard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:21.940399+00:00
-- url     : https://prove2.me/submissions/fa96d8fc-0762-43b4-8061-230d2056800b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicProfiles

section

open scoped BigOperators
open ConsistentSubmodular

theorem solution {m : ℕ} {p : Point m} (h : supportCard p ≤ 2) :
    ∃ a b : Fin (m + 1), ∀ i, i ≠ a → i ≠ b → p i = 0 := by
  classical
  obtain ⟨S, hSdef, hS2⟩ : ∃ S : Finset (Fin (m + 1)), (∀ i, p i ≠ 0 → i ∈ S) ∧ S.card ≤ 2 := by
    refine ⟨_, fun i hi => ?_, h⟩
    simp [hi]
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    refine ⟨0, 0, fun i _ _ => ?_⟩
    by_contra hi
    simpa [h0] using hSdef i hi
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, a, fun i hia _ => ?_⟩
    by_contra hi
    exact hia (Finset.mem_singleton.mp (hSdef i hi))
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2
    refine ⟨a, b, fun i hia hib => ?_⟩
    by_contra hi
    rcases Finset.mem_insert.mp (hSdef i hi) with h | h
    · exact hia h
    · exact hib (Finset.mem_singleton.mp h)

end
