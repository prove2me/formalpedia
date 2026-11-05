-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_positive_band_two_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:24:08.554729+00:00
-- url     : https://prove2.me/submissions/37fbd7e0-9009-4ac6-b457-db64a829f2aa

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_positive_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Two finite moment limits agree on positive-band continuous tests even if
a logarithmic transform has irrelevant nonzero values on negative arguments. -/
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
    (g : ℝ → ℝ) (hg : Continuous g) (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    (∫ z : ℝ, g z ∂μ) = (∫ z : ℝ, g z ∂ν) := by
  have hleft : Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_of_positive_band
      l μi μ hpositive_i hunit_μ hfinite_i hfinite_μ hmom_μ
      g hg δ hδ hzero_small hzero_upper
  have hright : Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂ν)) :=
    AvramDividend.Classical.avram_p2_i_moment_compact_test_of_positive_band
      l μi ν hpositive_i hunit_ν hfinite_i hfinite_ν hmom_ν
      g hg δ hδ hzero_small hzero_upper
  exact tendsto_nhds_unique hleft hright
