-- Prove2me | solution 1 for AvramDividend.Classical.small_positive_deficit_integral_le_laplace_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:58:33.704714+00:00
-- url     : https://prove2.me/submissions/8d2aaaf3-488c-4c57-a8fc-402459daaec3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A small strictly positive deficit is controlled by the nonzero part
    of its Laplace transform. The estimate is pointwise before integration. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (n a : ℝ)
    (hLeft : Integrable
      (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) μ)
    (hRight : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ) :
    (∫ ω, if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0 ∂μ) ≤
      Real.exp a *
        (∫ ω, if D ω = 0 then (0 : ℝ)
          else Real.exp (-(n * D ω)) ∂μ) := by
  have hPoint (ω : Ω) :
      (if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) ≤
        Real.exp a *
          (if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) := by
    by_cases hRange : 0 < D ω ∧ n * D ω ≤ a
    · have hNonzero : D ω ≠ 0 := ne_of_gt hRange.1
      simp only [if_pos hRange, if_neg hNonzero]
      have hBound : 0 ≤ a + -(n * D ω) := by
        simpa only [sub_eq_add_neg] using sub_nonneg.mpr hRange.2
      calc
        (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp (a + -(n * D ω)) :=
          (Real.exp_le_exp).mpr hBound
        _ = Real.exp a * Real.exp (-(n * D ω)) := Real.exp_add _ _
    · by_cases hZero : D ω = 0
      · simp [hRange, hZero]
      · simpa [hRange, hZero] using
          mul_nonneg (Real.exp_nonneg a) (Real.exp_nonneg (-(n * D ω)))
  calc
    (∫ ω, if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0 ∂μ) ≤
        ∫ ω, Real.exp a *
          (if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) ∂μ := by
          exact integral_mono_ae hLeft (hRight.const_mul _) (Filter.Eventually.of_forall hPoint)
    _ = Real.exp a *
        (∫ ω, if D ω = 0 then (0 : ℝ)
          else Real.exp (-(n * D ω)) ∂μ) := integral_const_mul _ _
