-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_C1_automatic_uniform_physical_negative_levy_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:51:37.529429+00:00
-- url     : https://prove2.me/submissions/87ee64fc-8deb-42ae-9d02-309bcfd4ffe9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV C¹ positive-cap hypotheses automatically produce a finite
uniform bound for the full physical negative-jump generator integral. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (C : ℝ≥0∞) (w : ℝ → ℝ)
  (hwCont : ContinuousOn w (Ici 0))
  (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
  (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
  (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hBand : Icc (a / 2) b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Icc a b,
    |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| ≤ M := by
  have hwMeas : Measurable w :=
    avram_wave8_22_original_BV_value_measurable_of_positive_continuity
      w hwCont hwNeg
  obtain ⟨L, hLip⟩ :=
    avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
      X hBV C w hwC1 (a / 2) b (by linarith) hBand
  obtain ⟨R, hR0, hWbound⟩ :=
    avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
      w hwCont hwNeg b (by linarith)
  have hMass : X.ν (Iic (-a / 2)) < ⊤ :=
    avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
      X a ha ha2
  exact avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
    X hBV w hwMeas a b (L : ℝ) R ha ha2 hab
      (NNReal.coe_nonneg _) hR0 hLip hWbound hMass
