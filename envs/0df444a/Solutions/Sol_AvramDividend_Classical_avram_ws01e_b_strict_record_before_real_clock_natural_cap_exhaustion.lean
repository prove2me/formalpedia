-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:54:04.277773+00:00
-- url     : https://prove2.me/submissions/61560667-713e-4058-aeb9-f2f5c569b57c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

/-- A finite real observation clock localises every strict ENNReal exit
before that clock into a natural finite deterministic cap. -/
theorem solution
    {Ω Θ : Type*}
    (τ : Ω → ℝ≥0∞) (clock : Θ → ℝ) :
    {z : Ω × Θ | τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} =
      ⋃ n : ℕ, {z : Ω × Θ |
        τ z.1 < (n : ℝ≥0∞) ∧
        τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.toNNReal (clock z.2))
    refine ⟨n, ?_, h⟩
    have hbound : (Real.toNNReal (clock z.2) : ℝ≥0∞) <
        (n : ℝ≥0∞) := by exact_mod_cast hn
    exact lt_trans h hbound
  · rintro ⟨n, _, h⟩
    exact h
