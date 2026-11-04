-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:47:12.007478+00:00
-- url     : https://prove2.me/submissions/8caad396-e13e-4f35-a9f4-2f0453756c8b

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_total_mass_of_zero_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_finite_lintegrals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Every moment, including the total-mass moment, supplies its own finiteness hypothesis. -/
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
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by
  have hfinite_i (i : ι) : (μi i) Set.univ < ⊤ :=
    AvramDividend.Classical.avram_p2_i_moment_total_mass_of_zero_lintegral
      (μi i) (hmom_i_finite i 0)
  have hfinite_μ : μ Set.univ < ⊤ :=
    AvramDividend.Classical.avram_p2_i_moment_total_mass_of_zero_lintegral
      μ (hmom_μ_finite 0)
  exact AvramDividend.Classical.avram_p2_i_moment_compact_test_of_finite_lintegrals
    l μi μ hfinite_i hfinite_μ hpositive_i hunit_μ
    hmom_i_finite hmom_μ_finite hmom g hg hg0
