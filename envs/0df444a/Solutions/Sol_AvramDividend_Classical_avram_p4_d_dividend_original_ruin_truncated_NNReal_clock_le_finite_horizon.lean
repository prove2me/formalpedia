-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:37:49.586439+00:00
-- url     : https://prove2.me/submissions/bc87efc2-5009-4180-a3fd-beecdc455741

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original ruin-truncated dividend stopping clock never exceeds
the natural-number horizon, including paths with infinite ruin time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, τ ω ≤ (n : ℝ≥0) := by
  intro ω
  rw [hτeq ω]
  have hle :
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤
        (n : ℝ≥0∞).toNNReal :=
    ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
  simpa using hle
