-- Prove2me | solution 1 for DeletedPrimes.decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:01:49.83302+00:00
-- url     : https://prove2.me/submissions/486bd5ab-0a81-4f4a-9793-ef7e751a9717

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {u j α : ℝ} {k : ℕ} (hα : 0 < α) (hu : 0 ≤ u) (hj0 : 0 ≤ j) (hjk : j ≤ k * u) :
    ∃ n : ℕ, n ≤ k ∧ (n : ℝ) * u ≤ j ∧
      (j - n * u ≤ α * u ∨ (α * u < j - n * u ∧ j < ((n : ℝ) + 1) * u ∧ n + 1 ≤ k)) := by
  rcases hu.eq_or_lt with hu0 | hupos
  · subst hu0
    refine ⟨0, Nat.zero_le _, ?_, Or.inl ?_⟩
    · simpa using hj0
    · simp only [mul_zero] at hjk ⊢; linarith
  · obtain ⟨n, h1, h2⟩ : ∃ n : ℕ, (n : ℝ) ≤ j / u ∧ j / u < n + 1 :=
      ⟨⌊j / u⌋₊, Nat.floor_le (div_nonneg hj0 hupos.le), Nat.lt_floor_add_one _⟩
    have h1' : (n : ℝ) * u ≤ j := (le_div_iff₀ hupos).1 h1
    have h2' : j < (n + 1) * u := (div_lt_iff₀ hupos).1 h2
    have hnk : n ≤ k := by
      have : (n : ℝ) ≤ k := le_of_mul_le_mul_right (h1'.trans hjk) hupos
      exact_mod_cast this
    refine ⟨n, hnk, h1', ?_⟩
    by_cases hr : j - n * u ≤ α * u
    · exact Or.inl hr
    · push Not at hr
      refine Or.inr ⟨hr, h2', ?_⟩
      have hne : n ≠ k := by
        intro h
        rw [h] at hr
        have := mul_pos hα hupos
        linarith
      omega
end DeletedPrimes
