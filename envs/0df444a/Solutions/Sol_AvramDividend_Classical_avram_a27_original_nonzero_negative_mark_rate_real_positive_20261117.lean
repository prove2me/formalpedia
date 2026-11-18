-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:26:36.35229+00:00
-- url     : https://prove2.me/submissions/5c2fea63-2e88-4501-916d-d1f95ac6f0a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a105_original_nonzero_negative_levy_measure_strict_negative_intensity_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Nonzero original negative Lévy intensity has positive finite real mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hNu : X.ν ≠ 0) :
    0 < (X.ν (Iio (0 : ℝ))).toReal := by
  have hPositive :=
    avram_a105_original_nonzero_negative_levy_measure_strict_negative_intensity_20261114
      X hNu
  have hNe : X.ν (Iio (0 : ℝ)) ≠ 0 := ne_of_gt hPositive
  exact ENNReal.toReal_pos hNe hFinite
