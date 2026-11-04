-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_original_normalized_image_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:57:31.65062+00:00
-- url     : https://prove2.me/submissions/56977c23-4293-4da3-92db-c63bc5905dba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_positive_ae_of_nonpositive_mass_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_nonpositive_null

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual time-normalised weighted exponential law has positive support at every real time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ) :
    ∀ᵐ z ∂(if 0 < h then (ENNReal.ofReal h)⁻¹ •
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
      else (0 : Measure ℝ)), 0 < z := by
  exact AvramDividend.Classical.avram_p2_i_moment_positive_ae_of_nonpositive_mass_zero _
    (AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_nonpositive_null X h)
