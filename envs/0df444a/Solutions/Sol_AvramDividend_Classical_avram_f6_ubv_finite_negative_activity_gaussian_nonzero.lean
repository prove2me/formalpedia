-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_ubv_finite_negative_activity_gaussian_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:17:55.814183+00:00
-- url     : https://prove2.me/submissions/1315617b-98de-4d88-892b-19c7896da457

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_negative_jump_intensity_infinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    X.σ ≠ 0 := by
  intro hσ
  exact hFiniteActivity
    (avram_f6_purejump_ubv_negative_jump_intensity_infinite X hBV hσ)
