-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:52:12.771168+00:00
-- url     : https://prove2.me/submissions/951e13a2-a8d1-4032-aa15-c1a547b8057b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_pure_jump_unbounded_variation_infinite_negative_activity
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    0 < X.σ := by
  have hnonzero : X.σ ≠ 0 := by
    intro hσ
    have hInfinity := pure_jump_unbounded_variation_infinite_negative_activity
      X hσ hBV
    exact (ne_of_lt hFinite) hInfinity
  exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hnonzero)
