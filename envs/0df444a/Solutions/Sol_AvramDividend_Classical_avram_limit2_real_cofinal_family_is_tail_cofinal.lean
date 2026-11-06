-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_real_cofinal_family_is_tail_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:46:27.445274+00:00
-- url     : https://prove2.me/submissions/47824b65-70c0-426e-ae9a-2fa9e75e34b3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- A real horizon sequence unbounded above remains cofinal after
    discarding any finite prefix; no monotonicity is required. -/
theorem solution
    (T : ℕ → ℝ)
    (hCofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k) :
    ∀ (N : ℕ) (a : ℝ), ∃ k : ℕ, N ≤ k ∧ a ≤ T k := by
  intro N a
  have hPrefix (n : ℕ) : ∃ M : ℝ, ∀ k < n, T k ≤ M := by
    induction n with
    | zero =>
      refine ⟨0, ?_⟩
      intro k hk
      exact (Nat.not_lt_zero k hk).elim
    | succ n ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨max M (T n), ?_⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact (hM k h).trans (le_max_left _ _)
      · exact le_max_right _ _
  obtain ⟨M, hM⟩ := hPrefix N
  obtain ⟨k, hk⟩ := hCofinal (max a M + 1)
  refine ⟨k, ?_, ?_⟩
  · by_contra hn
    have hklt : k < N := Nat.lt_of_not_ge hn
    have hle : T k ≤ M := hM k hklt
    have hmax : M ≤ max a M := le_max_right a M
    linarith
  · have hamax : a ≤ max a M := le_max_left a M
    linarith
