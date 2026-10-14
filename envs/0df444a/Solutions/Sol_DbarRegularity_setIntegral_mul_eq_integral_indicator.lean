-- Prove2me | solution 1 for DbarRegularity.setIntegral_mul_eq_integral_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:08:12.664887+00:00
-- url     : https://prove2.me/submissions/ba5abd1c-74bb-4441-86aa-4add69418e3c

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar



namespace DbarRegularity

open MeasureTheory Set

/-- The truncated singular integral as a convolution with the truncated kernel. -/
theorem setIntegral_mul_eq_integral_indicator {d : ℕ} (K f : EuclideanSpace ℝ (Fin d) → ℂ)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y =
      ∫ y, {y | ε ≤ ‖y‖}.indicator K (x - y) * f y := by
  rw [← integral_indicator (measurableSet_le measurable_const measurable_norm)]
  have h1 : ({y : EuclideanSpace ℝ (Fin d) | ε ≤ ‖y‖}.indicator fun y => f (x - y) * K y) =
      fun y => f (x - y) * {y | ε ≤ ‖y‖}.indicator K y := by
    ext y; simp only [indicator]; split_ifs <;> simp
  rw [h1, ← integral_sub_left_eq_self _ volume x]
  congr 1; ext y
  rw [sub_sub_cancel, mul_comm]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set

theorem solution {d : ℕ} (K f : EuclideanSpace ℝ (Fin d) → ℂ)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y =
      ∫ y, {y | ε ≤ ‖y‖}.indicator K (x - y) * f y :=
  DbarRegularity.setIntegral_mul_eq_integral_indicator K f ε x
