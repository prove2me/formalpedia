-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_compact_unit_moment_test_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:58:56.750473+00:00
-- url     : https://prove2.me/submissions/b9937fe4-8e3b-43f3-b528-8d8299d97c41

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_positive_band
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_unit_support_high_moment_mass_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal

/-- For finite positive measures carried by the open unit interval, all
Hausdorff moments are automatically finite. Their convergence implies
convergence on continuous tests separated from both endpoints. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hopen_i : ∀ i, ∀ᵐ z ∂μi i, z ∈ Set.Ioo (0 : ℝ) 1)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by
  have hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z := by
    intro i
    filter_upwards [hopen_i i] with z hz
    exact hz.1
  have hunit_i : ∀ i, ∀ᵐ z ∂μi i, z ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [hopen_i i] with z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hmoment_i : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤ := by
    intro i k
    have hbound := avram_p2_i_moment_unit_support_high_moment_mass_bound
      (μi i) (hunit_i i) k
    exact ne_of_lt (lt_of_le_of_lt hbound (hfinite_i i))
  have hmoment_μ : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤ := by
    intro k
    have hbound := avram_p2_i_moment_unit_support_high_moment_mass_bound
      μ hunit_μ k
    exact ne_of_lt (lt_of_le_of_lt hbound hfinite_μ)
  exact avram_p2_i_moment_compact_test_of_positive_band
    l μi μ hpositive_i hunit_μ hmoment_i hmoment_μ
    hmom g hg δ hδ hzero_small hzero_upper
