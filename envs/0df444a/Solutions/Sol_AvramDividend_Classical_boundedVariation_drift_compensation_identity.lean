-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_drift_compensation_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:01:48.942979+00:00
-- url     : https://prove2.me/submissions/374cfa6b-df10-4509-bd64-e41b8d21181b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Extract the compensated small-jump drift in the BV generator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) :
    X.c * deriv w x -
        ∫ y in Ioo (-1 : ℝ) 0, deriv w x * y ∂X.ν =
      X.drift * deriv w x := by
  have hInt := boundedVariation_smallJump_deriv_integrable X hBV w x
  rw [MeasureTheory.integral_const_mul]
  simp only [SpectrallyNegativeLevy.drift]
  ring
