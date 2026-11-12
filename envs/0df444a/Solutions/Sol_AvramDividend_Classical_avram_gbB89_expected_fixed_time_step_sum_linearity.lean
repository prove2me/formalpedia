-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB89_expected_fixed_time_step_sum_linearity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:58:07.891862+00:00
-- url     : https://prove2.me/submissions/25951783-67d1-4bfc-b6db-eacf3d32188b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : ℕ) (δ t : ℝ) (F : ℕ → Ω → ℝ)
    (hF : ∀ r, Integrable (F r) P) :
    (∫ ω, (Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then F r ω else 0) ∂P) =
    (Finset.range N).sum (fun r =>
      if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
      then (∫ ω, F r ω ∂P) else 0) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro r hr
    by_cases h : (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
    · simp only [if_pos h]
    · simp only [if_neg h, integral_zero]
  · intro r hr
    by_cases h : (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
    · simpa only [if_pos h] using hF r
    · have h' : ¬ ((r : ℝ) * δ ≤ t ∧
          t < ((r : ℝ) + 1) * δ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using h
      simp [h']
