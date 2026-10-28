-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_strict_record_before_clock_capped_reward_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:22:47.550011+00:00
-- url     : https://prove2.me/submissions/b738d5e9-33a9-422d-87b2-d36552b3ba79

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_before_clock_capped_mass_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Weighted monotone cap removal for a genuine nonnegative path-clock reward. -/
theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure (Ω × Θ))
    (τ : Ω → ℝ≥0∞) (clock : Θ → ℝ)
    (F : Ω × Θ → ℝ≥0∞) (hF : Measurable F)
    (hMeas : ∀ n : ℕ, MeasurableSet {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}) :
    (∫⁻ z in {z : Ω × Θ |
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}, F z ∂μ) =
    ⨆ n : ℕ, (∫⁻ z in {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}, F z ∂μ) := by
  let A : ℕ → Set (Ω × Θ) := fun n =>
    {z : Ω × Θ | τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}
  let B : Set (Ω × Θ) :=
    {z : Ω × Θ | τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}
  have hB : MeasurableSet B := by
    change MeasurableSet
      {z : Ω × Θ | τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)}
    rw [avram_ws01e_b_strict_record_before_real_clock_natural_cap_exhaustion τ clock]
    exact MeasurableSet.iUnion hMeas
  have hMass :=
    avram_ws01e_b_strict_record_before_clock_capped_mass_iSup
      (μ.withDensity F) τ clock hMeas
  change (μ.withDensity F) B = ⨆ n : ℕ, (μ.withDensity F) (A n) at hMass
  change (∫⁻ z in B, F z ∂μ) = ⨆ n : ℕ, (∫⁻ z in A n, F z ∂μ)
  calc
    (∫⁻ z in B, F z ∂μ) = (μ.withDensity F) B :=
      (withDensity_apply F hB).symm
    _ = ⨆ n : ℕ, (μ.withDensity F) (A n) := hMass
    _ = ⨆ n : ℕ, (∫⁻ z in A n, F z ∂μ) := by
      congr 1
      funext n
      exact withDensity_apply F (hMeas n)
