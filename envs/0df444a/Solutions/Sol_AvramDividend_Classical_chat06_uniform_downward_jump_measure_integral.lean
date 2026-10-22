-- Prove2me | solution 1 for AvramDividend.Classical.chat06_uniform_downward_jump_measure_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:19:43.354297+00:00
-- url     : https://prove2.me/submissions/08db5f2f-1dce-4c7c-8403-22d0df6080a4

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real

namespace AvramChat06

/-- The Lévy measure of rate-one uniform downward jumps
is a unit-density restriction to (-2,-1). Its exponential
moment reduces to the elementary signed interval integral
without introducing an abstract Fourier/Laplace transform. -/
theorem uniform_downward_jump_measure_integral (θ : ℝ) :
    (∫ y, Real.exp (θ * y)
      ∂((volume : Measure ℝ).restrict (Ioo (-2 : ℝ) (-1 : ℝ)))) =
    ∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y) := by
  change (∫ y in Ioo (-2 : ℝ) (-1 : ℝ), Real.exp (θ * y)) =
    ∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y)
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1)]

end AvramChat06

open AvramChat06

theorem solution (θ : ℝ) :
    (∫ y, Real.exp (θ * y)
      ∂((volume : Measure ℝ).restrict (Ioo (-2 : ℝ) (-1 : ℝ)))) =
    ∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y) := by
  exact uniform_downward_jump_measure_integral θ
