-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:52:33.582615+00:00
-- url     : https://prove2.me/submissions/370fb83f-a68d-4ec0-af5d-3f0f75c14467

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal
noncomputable section

/-- On a finite physical grid, the original masked residual separates exactly
    into a ruin-clipped residual and the discarded contact increment. -/
theorem solution
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0) (R : ℝ≥0 → ℝ)
    (W : ℕ → ℝ) (E : ℕ → Prop)
    (hE : ∀ i, E i → u i < τ) :
    (∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0) =
      (∑ i ∈ Finset.range n,
        if E i then
          W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0) +
      (∑ i ∈ Finset.range n,
        if E i then
          W i * (R (min (u (i + 1)) τ) - R (u (i + 1))) else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : E i
  · simp only [if_pos h]
    have hmin : min (u i) τ = u i :=
      min_eq_left (le_of_lt (hE i h))
    rw [hmin]
    ring
  · simp [h]
