-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_finite_unit_ennreal_moment_measures_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:02:12.259633+00:00
-- url     : https://prove2.me/submissions/b174df4a-ed63-4dc1-ad67-d711d3e32eb2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_unit_support_high_moment_mass_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_integrable_of_lintegral_ne_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal

/-- Full Borel Hausdorff uniqueness without auxiliary integrability or
moment-finiteness hypotheses for finite unit-supported positive measures. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hunit_ν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) :
    μ = ν := by
  have hfinite (σ : Measure ℝ) [IsFiniteMeasure σ]
      (hunit : ∀ᵐ z ∂σ, z ∈ Icc (0 : ℝ) 1) (k : ℕ) :
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂σ) ≠ ⊤ := by
    have hb := avram_p2_i_moment_unit_support_high_moment_mass_bound σ hunit k
    exact ne_of_lt (lt_of_le_of_lt hb (measure_lt_top σ Set.univ))
  have hreal (σ : Measure ℝ) [IsFiniteMeasure σ]
      (hunit : ∀ᵐ z ∂σ, z ∈ Icc (0 : ℝ) 1) (k : ℕ) :
      Integrable (fun z : ℝ => z ^ k) σ := by
    have hp : ∀ᵐ z ∂σ, 0 ≤ z := hunit.mono (fun z hz => hz.1)
    exact avram_p2_i_moment_integrable_of_lintegral_ne_top
      σ hp k (hfinite σ hunit k)
  exact avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
    μ ν hunit_μ hunit_ν
    (fun k => hreal μ hunit_μ k) (fun k => hreal ν hunit_ν k)
    (fun k => hfinite ν hunit_ν k) hmom
