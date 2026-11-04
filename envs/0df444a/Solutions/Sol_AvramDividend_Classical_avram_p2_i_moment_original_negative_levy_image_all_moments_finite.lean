-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_original_negative_levy_image_all_moments_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:58:11.569189+00:00
-- url     : https://prove2.me/submissions/063350a6-c099-443d-bc09-e7b8e35e6d58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_unit_support_high_moment_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual finite negative Lévy weighted-image law has all nonnegative moments finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)) ≠ ⊤ := by
  let η : Measure ℝ :=
    ((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp
  have hfinite : η Set.univ < ⊤ := by
    letI : IsFiniteMeasure η :=
      avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite X
    exact measure_lt_top _ _
  have hsupp : ∀ᵐ z ∂η, z ∈ Icc (0 : ℝ) 1 := by
    apply ae_iff.mpr
    exact avram_p2_negative_levy_weighted_exp_image_compact_support X
  change (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η) ≠ ⊤
  exact ne_of_lt (lt_of_le_of_lt
    (avram_p2_i_moment_unit_support_high_moment_mass_bound η hsupp k)
    hfinite)
