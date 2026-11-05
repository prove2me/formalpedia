-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_two_moment_limits_compact_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:21:54.156202+00:00
-- url     : https://prove2.me/submissions/0a5ed5e0-b138-4de6-8318-bca909553929

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_lintegral_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Two unit-supported finite moment limits of the same positive measure
family agree on all continuous tests supported in the open unit band. -/
theorem solution
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (μi : ι → Measure ℝ) (μ ν : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hunit_ν : ∀ᵐ z ∂ν, z ∈ Set.Icc (0 : ℝ) 1)
    (hfinite_i : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hfinite_μ : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hfinite_ν : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν) ≠ ⊤)
    (hmom_μ : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (hmom_ν : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂μ) = (∫ z : ℝ, g z ∂ν) := by
  have hleft : Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral_moments
      l μi μ hpositive_i hunit_μ hfinite_i hfinite_μ hmom_μ g hg hg0
  have hright : Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂ν)) :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral_moments
      l μi ν hpositive_i hunit_ν hfinite_i hfinite_ν hmom_ν g hg hg0
  exact tendsto_nhds_unique hleft hright
