-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn30_original_stopped_grid_mask_eq_bounded_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:30:28.890204+00:00
-- url     : https://prove2.me/submissions/6b8d210c-d162-48d7-895f-b505f87ce455

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Exact pathwise accounting of the original physical ruin-clock mask as a bounded stopping prefix. -/
theorem solution
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hkBound : ∀ ω, k ω ≤ m)
    (hMask : ∀ ω i, i < m →
      ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω))
    (Z : ℕ → Ω → ℝ) :
    ∀ ω, (∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then Z i ω else 0)
      = ∑ i ∈ Finset.range (k ω), Z i ω := by
  intro ω
  calc
    (∑ i ∈ Finset.range m, if (u i : WithTop ℝ≥0) < τ ω then Z i ω else 0) =
        ∑ i ∈ Finset.range m, if i < k ω then Z i ω else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [(hMask ω i (Finset.mem_range.mp hi))]
    _ = ∑ i ∈ Finset.range (k ω), Z i ω := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hi
        exact hi.2
      · intro hi
        exact ⟨lt_of_lt_of_le hi (hkBound ω), hi⟩
