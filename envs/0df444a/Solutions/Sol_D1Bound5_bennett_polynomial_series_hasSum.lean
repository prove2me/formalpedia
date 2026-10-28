-- Prove2me | solution 1 for D1Bound5.bennett_polynomial_series_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:32.632472+00:00
-- url     : https://prove2.me/submissions/59172547-09c6-4219-ac7c-4e3a4a7f2a96

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

/-- Multiplication by a polynomial commutes with analytic summation of a
power series.  Absolute summability makes the Cauchy-product step explicit. -/
theorem _root_.solution (P : Polynomial ℂ) (B : PowerSeries ℂ)
    (x b : ℂ)
    (hB : HasSum (fun r : ℕ => PowerSeries.coeff r B * x ^ r) b)
    (hBnorm : Summable (fun r : ℕ => ‖PowerSeries.coeff r B * x ^ r‖)) :
    HasSum (fun r : ℕ => PowerSeries.coeff r ((P : PowerSeries ℂ) * B) * x ^ r)
      (P.eval x * b) := by
  have hpzero (r : ℕ) (hr : r ∉ P.support) : P.coeff r * x ^ r = 0 := by
    rw [Polynomial.notMem_support_iff.mp hr, zero_mul]
  have hp : HasSum (fun r : ℕ => P.coeff r * x ^ r) (P.eval x) := by
    simpa only [Polynomial.eval_eq_sum, Polynomial.sum] using
      (hasSum_sum_of_ne_finset_zero (s := P.support) hpzero)
  have hpNorm : Summable (fun r : ℕ => ‖P.coeff r * x ^ r‖) := by
    apply summable_of_ne_finset_zero (s := P.support)
    intro r hr
    rw [hpzero r hr, norm_zero]
  have hc (r : ℕ) :
      PowerSeries.coeff r ((P : PowerSeries ℂ) * B) * x ^ r =
        ∑ uv ∈ antidiagonal r,
          (P.coeff uv.1 * x ^ uv.1) * (PowerSeries.coeff uv.2 B * x ^ uv.2) := by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro uv huv
    rw [Polynomial.coeff_coe, ← Finset.mem_antidiagonal.mp huv, pow_add]
    ring
  have hconv :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hpNorm hBnorm
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hpNorm hBnorm
  rw [hp.tsum_eq, hB.tsum_eq] at heq
  have hh := hconv.of_norm.hasSum
  rw [← heq] at hh
  simpa only [hc] using hh



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]







end Nodes

end D1Bound5
end
