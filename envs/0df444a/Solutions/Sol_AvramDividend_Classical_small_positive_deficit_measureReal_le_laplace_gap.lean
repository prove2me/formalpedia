-- Prove2me | solution 1 for AvramDividend.Classical.small_positive_deficit_measureReal_le_laplace_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:14:16.280581+00:00
-- url     : https://prove2.me/submissions/04604ba1-41da-4bcb-88dc-aa86689462f3

import Theorems.Thm_AvramDividend_Classical_small_positive_deficit_integral_le_laplace_nonzero
import Theorems.Thm_AvramDividend_Classical_nonzero_laplace_integral_eq_total_sub_zero_atom
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The probability of a small strictly positive deficit is bounded by
    its full Laplace transform with the zero atom subtracted. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (n a : ℝ)
    (hSmallMeas : MeasurableSet {ω : Ω | 0 < D ω ∧ n * D ω ≤ a})
    (hZeroMeas : MeasurableSet {ω : Ω | D ω = 0})
    (hLeft : Integrable
      (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) μ)
    (hRight : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ)
    (hZero : Integrable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) μ) :
    μ.real {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} ≤
      Real.exp a *
        ((∫ ω, Real.exp (-(n * D ω)) ∂μ) -
          μ.real {ω : Ω | D ω = 0}) := by
  classical
  have hSmallIntegral :
      (∫ ω, if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0 ∂μ) =
        μ.real {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one hSmallMeas)
  have hZeroIntegral :
      (∫ ω, if D ω = 0 then (1 : ℝ) else 0 ∂μ) =
        μ.real {ω : Ω | D ω = 0} := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one hZeroMeas)
  calc
    μ.real {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} =
        (∫ ω, if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0 ∂μ) :=
      hSmallIntegral.symm
    _ ≤ Real.exp a *
        (∫ ω, if D ω = 0 then (0 : ℝ)
          else Real.exp (-(n * D ω)) ∂μ) :=
      small_positive_deficit_integral_le_laplace_nonzero
        μ D n a hLeft hRight
    _ = Real.exp a *
        ((∫ ω, Real.exp (-(n * D ω)) ∂μ) -
          μ.real {ω : Ω | D ω = 0}) := by
      rw [nonzero_laplace_integral_eq_total_sub_zero_atom
        μ D n hRight hZero, hZeroIntegral]
