-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_terminal_W_survival_horizon_branch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:40:34.006201+00:00
-- url     : https://prove2.me/submissions/542742c2-6d35-4426-97f5-2b09f9d61732

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- True source W chooses its postpayment branch by zero clock or survival horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω =
      if τ ω = 0 ∨ (n : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω := by
  intro ω
  have hClock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hBefore : (τ ω : ℝ≥0∞) < ruinTime X x D ω ↔
      (n : ℝ≥0∞) < ruinTime X x D ω := by
    rw [hτeq ω, hClock.1 ω]
    simp [min_lt_iff]
  simpa only [hBefore] using hW ω
