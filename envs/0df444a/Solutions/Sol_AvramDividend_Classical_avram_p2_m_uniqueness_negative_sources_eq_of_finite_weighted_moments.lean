-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_negative_sources_eq_of_finite_weighted_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:56:13.812999+00:00
-- url     : https://prove2.me/submissions/24e1897c-0cb4-4210-bb4f-1a3417f291d4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal

/-- Genuine finite weighted exponential moments determine arbitrary
strictly negative source measures, without regularity assumptions. -/
theorem solution
    (μ ν η ρ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ]
    (hnegμ : ∀ᵐ y ∂μ, y < 0)
    (hnegν : ∀ᵐ y ∂ν, y < 0)
    (hη : η = ((μ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hρ : ρ = ((ν.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂η) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ)) :
    μ = ν := by
  have hunitη : ∀ᵐ z ∂η, z ∈ Icc (0 : ℝ) 1 := by
    rw [hη]
    exact avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
      μ hnegμ
  have hunitρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1 := by
    rw [hρ]
    exact avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
      ν hnegν
  have heq : η = ρ :=
    avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
      η ρ hunitη hunitρ hmom
  apply avram_p2_m_uniqueness_negative_exp_fourth_weighted_source_measure_ext
    μ ν hnegμ hnegν
  exact hη.symm.trans (heq.trans hρ)
