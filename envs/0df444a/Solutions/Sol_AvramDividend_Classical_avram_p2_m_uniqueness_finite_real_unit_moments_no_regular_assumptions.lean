-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_finite_real_unit_moments_no_regular_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:53:59.253194+00:00
-- url     : https://prove2.me/submissions/4e1376fb-a767-4acb-86bc-20d243b5ca7f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_finite_unit_ennreal_moment_measures_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal

/-- Finite Borel measures on the real line are regular, so all Hausdorff
moments identify unit-supported measures without a regularity premise. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hunitμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hunitν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) :
    μ = ν := by
  letI : μ.Regular := inferInstance
  letI : ν.Regular := inferInstance
  exact avram_p2_m_uniqueness_finite_unit_ennreal_moment_measures_eq
    μ ν hunitμ hunitν hmom
