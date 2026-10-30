-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_random_record_shifted_rational_survival_ae_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:09:26.328197+00:00
-- url     : https://prove2.me/submissions/3e38b3fd-6318-4621-a63a-496cd88b893c

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_shifted_rational_future_ae_closed_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Translate the genuine shifted Lévy future rational/closed survival
almost-everywhere equivalence by each realised first-record clock τ(ω). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) :
    ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      (0 ≤ r - (τ ω : ℝ) ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
            Real.toNNReal (r - (τ ω : ℝ)) →
          0 ≤ a + (X.X (τ ω + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω -
            X.X (τ ω) ω)) ↔
      (0 ≤ r - (τ ω : ℝ) ∧ ∀ s : ℝ≥0,
        s ≤ Real.toNNReal (r - (τ ω : ℝ)) →
          0 ≤ a + (X.X (τ ω + s) ω - X.X (τ ω) ω)) := by
  exact (eventually_sub_right_iff
    (volume : Measure ℝ) (τ ω : ℝ)).mpr
      (avram_ws01h_shifted_rational_future_ae_closed_survival
        X a ω (τ ω))
