-- Prove2me | solution 1 for AvramDividend.Classical.weighted_jump_integral_affine_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:57:41.31232+00:00
-- url     : https://prove2.me/submissions/06eab5c4-4b69-4472-abed-f3f4ba3915b6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Integrate a compensated jump term without losing its affine boundary part. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F K : α → ℝ) (a b c : ℝ)
    (hF : Integrable F μ) (hK : Integrable K μ) :
    (∫ y, ((F y - a * K y) * b + K y * c) ∂μ) =
      ((∫ y, F y ∂μ) - a * (∫ y, K y ∂μ)) * b +
      (∫ y, K y ∂μ) * c := by
  have hAK : Integrable (fun y => a * K y) μ := hK.const_mul a
  have hsub : Integrable (fun y => F y - a * K y) μ := hF.sub hAK
  calc
    (∫ y, ((F y - a * K y) * b + K y * c) ∂μ) =
        (∫ y, (F y - a * K y) * b ∂μ) +
        (∫ y, K y * c ∂μ) :=
      integral_add (hsub.mul_const b) (hK.mul_const c)
    _ = ((∫ y, F y ∂μ) - a * (∫ y, K y ∂μ)) * b +
        (∫ y, K y ∂μ) * c := by
      rw [integral_mul_const, integral_mul_const, integral_sub hF hAK,
        integral_const_mul]
