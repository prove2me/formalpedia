-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_original_levy_weighted_log_test_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:03:08.66064+00:00
-- url     : https://prove2.me/submissions/f9797abc-3747-48f2-858e-1b806f4c9915

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_normalized_image_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_levy_image_all_moments_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_positive_band
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weighted_log_positive_band_test
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_kmoment_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_moments_converge
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original-process fourth-weighted log tests converge to the original Lévy image. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Tendsto (fun h : ℝ => ∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
      (if 0 < h then (ENNReal.ofReal h)⁻¹ •
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
       else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))) := by
  let μh (h : ℝ) : Measure ℝ :=
    if 0 < h then (ENNReal.ofReal h)⁻¹ •
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
    else 0
  let η : Measure ℝ :=
    ((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp
  obtain ⟨hg, ⟨δ, hδ, hzero_small, hzero_upper⟩⟩ :=
    avram_p2_i_moment_weighted_log_positive_band_test
      f hf a ε hε hflower hfupper
  have hp : ∀ h, ∀ᵐ z ∂μh h, 0 < z := by
    intro h
    exact avram_p2_i_moment_original_normalized_image_positive_ae X h
  have hs : ∀ᵐ z ∂η, z ∈ Icc (0 : ℝ) 1 := by
    apply ae_iff.mpr
    exact avram_p2_negative_levy_weighted_exp_image_compact_support X
  have hfi : ∀ h k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μh h) ≠ ⊤ := by
    intro h k
    by_cases hh : 0 < h
    · have ht := avram_p2_k_original_normalized_weighted_image_kmoment_finite
        X h hh k
      exact ne_of_lt (by simpa only [μh, if_pos hh] using ht)
    · simp [μh, hh]
  have hfη : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η) ≠ ⊤ := by
    intro k
    exact avram_p2_i_moment_original_negative_levy_image_all_moments_finite X k
  have hm : ∀ k, Tendsto
      (fun h : ℝ => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μh h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η)) := by
    intro k
    exact avram_p2_k_original_normalized_weighted_image_moments_converge X k
  change Tendsto
    (fun h : ℝ => ∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂μh h)
    (nhdsWithin (0 : ℝ) (Ioi 0))
    (nhds (∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂η))
  exact avram_p2_i_moment_compact_test_of_positive_band
    (nhdsWithin (0 : ℝ) (Ioi 0)) μh η
    hp hs hfi hfη hm
    (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4)
    hg δ hδ hzero_small hzero_upper
