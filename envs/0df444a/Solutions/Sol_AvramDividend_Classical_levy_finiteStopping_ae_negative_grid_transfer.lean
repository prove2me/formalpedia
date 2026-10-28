-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_ae_negative_grid_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:34:34.277818+00:00
-- url     : https://prove2.me/submissions/70d10a9b-4541-4377-b0a0-5c612c0d7c4d

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedPath_ae_event_transfer
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hOrigMeas : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω))
    (times horizons : ℕ → ℝ≥0)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧
        X.X (τ ω + times m) ω - X.X (τ ω) ω < 0 := by
  let G : Set (ℝ≥0 → ℝ) :=
    {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ f (times m) < 0}
  have hG : MeasurableSet G :=
    measurableSet_countable_schedule_negative_near_zero times horizons
  exact levy_finiteStopping_shiftedPath_ae_event_transfer
    X τ hτ hstop hOrigMeas G hG hGridAE
