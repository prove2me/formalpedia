-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_compact_test_of_positive_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:48:35.080205+00:00
-- url     : https://prove2.me/submissions/3aa92b7a-0c67-42cd-8050-c2057d80cd69

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_positive_cutoff_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_lintegral_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Positive image measures only see the nonnegative part of a compact test. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hmom_i_finite : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hmom_μ_finite : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by
  obtain ⟨u, hu, huoutside, hueq⟩ :=
    AvramDividend.Classical.avram_p2_i_moment_positive_cutoff_continuous
      g hg δ hδ hzero_small hzero_upper
  have hconv :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral_moments
      l μi μ hpositive_i hunit_μ
      hmom_i_finite hmom_μ_finite hmom u hu huoutside
  have hEq_i (i : ι) :
      (∫ z : ℝ, u z ∂μi i) = ∫ z : ℝ, g z ∂μi i := by
    apply integral_congr_ae
    filter_upwards [hpositive_i i] with z hz
    exact hueq z hz.le
  have hEq_μ :
      (∫ z : ℝ, u z ∂μ) = ∫ z : ℝ, g z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hunit_μ] with z hz
    exact hueq z hz.1
  have hEq_fun :
      (fun i => ∫ z : ℝ, u z ∂μi i) =
      (fun i => ∫ z : ℝ, g z ∂μi i) := by
    funext i
    exact hEq_i i
  rw [hEq_fun, hEq_μ] at hconv
  exact hconv
