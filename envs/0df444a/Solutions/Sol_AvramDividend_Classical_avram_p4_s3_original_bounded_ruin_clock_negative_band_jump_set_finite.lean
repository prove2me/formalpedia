-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_ruin_clock_negative_band_jump_set_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:45:08.610482+00:00
-- url     : https://prove2.me/submissions/777881ca-c910-4c0d-a554-bc0f95213319

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped negative-band jump times form a genuine finite set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T) (ω : Ω) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.Finite := by
  apply (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).subset
  intro u hu
  exact ⟨hu.1, (hu.2.1).trans (hτ ω), hu.2.2⟩
