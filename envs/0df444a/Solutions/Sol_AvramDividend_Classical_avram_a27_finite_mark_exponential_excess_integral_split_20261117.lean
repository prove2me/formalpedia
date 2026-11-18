-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_mark_exponential_excess_integral_split_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:23:52.322958+00:00
-- url     : https://prove2.me/submissions/440a5521-d1d8-4867-9a6f-42bc4735b8ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The finite mark exponential excess integral is the mark moment minus total intensity. -/
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (θ : ℝ)
    (hInt : Integrable (fun y : ℝ => Real.exp (θ * y)) μ) :
    (∫ y, Real.exp (θ * y) - 1 ∂μ) =
      (∫ y, Real.exp (θ * y) ∂μ) - μ.real Set.univ := by
  rw [integral_sub hInt (integrable_const (1 : ℝ))]
  simp
