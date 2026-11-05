-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_original_levy_image_moment_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:26:13.093378+00:00
-- url     : https://prove2.me/submissions/1d6447a4-09a8-4dbe-ab7d-258c16d2e1ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_two_moment_limits_compact_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_moments_converge
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_original_normalized_weighted_image_kmoment_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_normalized_image_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_levy_image_all_moments_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original Lévy weighted negative image uniquely determines any
other compact-test limit having the same finite small-time moment limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Measure ℝ)
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunit_ρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
    (hfinite_ρ : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ) ≠ ⊤)
    (hmom_ρ : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)) =
      (∫ z : ℝ, g z ∂ρ) := by
  letI : (nhdsWithin (0 : ℝ) (Ioi 0)).NeBot := hne
  let μh (h : ℝ) : Measure ℝ :=
    if 0 < h then (ENNReal.ofReal h)⁻¹ •
      ((P.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
    else 0
  let η : Measure ℝ :=
    ((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp
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
  have hmη : ∀ k, Tendsto
      (fun h : ℝ => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μh h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η)) := by
    intro k
    exact avram_p2_k_original_normalized_weighted_image_moments_converge X k
  change (∫ z : ℝ, g z ∂η) = (∫ z : ℝ, g z ∂ρ)
  exact avram_p2_m_uniqueness_two_moment_limits_compact_tests
    (nhdsWithin (0 : ℝ) (Ioi 0)) μh η ρ
    hp hs hunit_ρ hfi hfη hfinite_ρ hmη hmom_ρ g hg hg0
