-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_scaled_signed_source_mean_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:38:51.395867+00:00
-- url     : https://prove2.me/submissions/6de973a1-6927-42e9-9d04-a5d60800bd1b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Multiplying a genuine signed source by deterministic nonnegative weights
preserves its joint L1 budget without separate component assumptions. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hZ : ∀ n, Integrable (Z n) P ∧
      (∫ ω, Z n ω ∂P) ≤ 0) :
    ∀ n, Integrable (fun ω => a n * Z n ω) P ∧
      (∫ ω, a n * Z n ω ∂P) ≤ 0 := by
  intro n
  refine ⟨(hZ n).1.const_mul (a n), ?_⟩
  rw [integral_const_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (ha n) (hZ n).2
