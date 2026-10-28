-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_strict_record_before_clock_capped_mass_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:01:18.629088+00:00
-- url     : https://prove2.me/submissions/39458f99-5b2e-42c2-b52d-cf085ce2f507

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure (Ω × Θ))
    (τ : Ω → ℝ≥0∞) (clock : Θ → ℝ)
    (hMeas : ∀ n : ℕ, MeasurableSet {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}) :
    μ {z : Ω × Θ |
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} =
    ⨆ n : ℕ, μ {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} := by
  let A : ℕ → Set (Ω × Θ) := fun n =>
    {z : Ω × Θ | τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}
  have hMono : Monotone A := by
    intro m n hmn z hz
    exact ⟨lt_of_lt_of_le hz.1 (by exact_mod_cast hmn), hz.2⟩
  rw [avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion τ clock]
  exact hMono.measure_iUnion
