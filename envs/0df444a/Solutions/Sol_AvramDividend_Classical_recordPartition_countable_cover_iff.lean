-- Prove2me | solution 1 for AvramDividend.Classical.recordPartition_countable_cover_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:07:48.961198+00:00
-- url     : https://prove2.me/submissions/c4ba4133-d0a4-4220-ace8-ee1e1a22de39

import Theorems.Thm_AvramDividend_Classical_recordPartition_finite_cover_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (x : ℝ) :
    u 0 < x ↔ ∃ i : ℕ, x ∈ Set.Ioc (u i) (u (i + 1)) := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := hcofinal x
    obtain ⟨i, hi, hlo, hhi⟩ :=
      (AvramDividend.Classical.recordPartition_finite_cover_iff u hu n x).mp
        ⟨hx, hn⟩
    exact ⟨i, ⟨hlo, hhi⟩⟩
  · rintro ⟨i, hi⟩
    exact lt_of_le_of_lt (hu (Nat.zero_le i)) hi.1
