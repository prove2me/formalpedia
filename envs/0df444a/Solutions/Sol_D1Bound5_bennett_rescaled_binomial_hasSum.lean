-- Prove2me | solution 1 for D1Bound5.bennett_rescaled_binomial_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:16.488165+00:00
-- url     : https://prove2.me/submissions/964fadde-4a8f-4852-ac77-e26e29189736

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5



/-- The rescaled formal binomial series evaluates to the principal complex
power in the unit disk, with absolute summability. -/
theorem _root_.solution (a ν x : ℂ) (hx : ‖a * x‖ < 1) :
    HasSum (fun r : ℕ =>
      PowerSeries.coeff r (PowerSeries.rescale a (PowerSeries.binomialSeries ℂ ν)) *
        x ^ r) ((1 + a * x) ^ ν) ∧
    Summable (fun r : ℕ =>
      ‖PowerSeries.coeff r
        (PowerSeries.rescale a (PowerSeries.binomialSeries ℂ ν)) * x ^ r‖) := by
  have hxball : a * x ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
  have hseries := Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := ν)
  have hs := hseries.hasSum_sub hxball
  have hxrad : a * x ∈ Metric.eball (0 : ℂ) (binomialSeries ℂ ν).radius :=
    lt_of_lt_of_le hxball hseries.r_le
  have hnorm := (binomialSeries ℂ ν).summable_norm_apply hxrad
  have hc (r : ℕ) :
      PowerSeries.coeff r (PowerSeries.rescale a (PowerSeries.binomialSeries ℂ ν)) *
        x ^ r = Ring.choose ν r * (a * x) ^ r := by
    simp only [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      smul_eq_mul, mul_one, mul_pow]
    ring
  constructor
  · simpa only [hc, sub_zero, binomialSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hs
  · simpa only [hc, binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, mul_comm] using hnorm

section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]







end Nodes

end D1Bound5
end
