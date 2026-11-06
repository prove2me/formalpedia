-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:21:43.421067+00:00
-- url     : https://prove2.me/submissions/1979707c-711f-43b4-9673-58dc4fffbb7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Both actual terminal branches use the same original Lévy process,
the intrinsic finite-band compensated jump integral, and its residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω =
      x + (τ ω : ℝ) * X.c +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (τ ω) ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω +
        avram_p4_h_gaussian_intrinsic_truncated_residual X n (τ ω) ω -
        (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
         then rightLimit D (τ ω) ω else D (τ ω) ω) := by
  intro ω
  by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simp only [hW ω, if_pos h,
      avram_p4_h_gaussian_intrinsic_truncated_residual]
    ring
  · simp only [hW ω, if_neg h, riskProcess,
      avram_p4_h_gaussian_intrinsic_truncated_residual]
    ring
