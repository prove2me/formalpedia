-- Prove2me | solution 1 for Farey.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T10:48:52.416053+00:00
-- url     : https://prove2.me/submissions/cb6fd409-16ff-41ac-b79d-1fa2d941860b

import Definitions.Def_Farey
import Mathlib

theorem solution {P : ℕ} {p : ℕ × ℕ} :
    p ∈ Farey.pairs P ↔ 1 ≤ p.1 ∧ p.1 ≤ P ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1 := by
  unfold Farey.pairs
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨q, ⟨hq1, hqP⟩, a, ⟨⟨ha1, haq⟩, hcop⟩, rfl⟩
    exact ⟨hq1, hqP, ha1, haq, hcop⟩
  · rintro ⟨hq1, hqP, ha1, haq, hcop⟩
    exact ⟨p.1, ⟨hq1, hqP⟩, p.2, ⟨⟨ha1, haq⟩, hcop⟩, rfl⟩
