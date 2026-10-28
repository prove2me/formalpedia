-- Prove2me | solution 1 for D1Bound5.bennett_positive_series_mul_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:21.20965+00:00
-- url     : https://prove2.me/submissions/0e5c6a36-12c6-4479-a958-c2779aa76f30

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Theorems.Thm_D1Bound5_bennett_positive_weighted_coeff_mul

section
open Finset

namespace D1Bound5















/-- Weighted Cauchy multiplication for positive real power series. The two
series are actually summable at the chosen radius; no formal evaluation is
silently treated as an analytic sum. -/
theorem _root_.solution
    (P Q : PowerSeries ℝ) (r s t : ℝ) (hr : 0 ≤ r)
    (hP : ∀ n, 0 ≤ PowerSeries.coeff n P)
    (hQ : ∀ n, 0 ≤ PowerSeries.coeff n Q)
    (hs : HasSum (fun n : ℕ => PowerSeries.coeff n P * r^n) s)
    (ht : HasSum (fun n : ℕ => PowerSeries.coeff n Q * r^n) t) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (P*Q) * r^n) (s*t) := by
  let f : ℕ → ℝ := fun n => PowerSeries.coeff n P * r ^ n
  let g : ℕ → ℝ := fun n => PowerSeries.coeff n Q * r ^ n
  have hf : HasSum f s := hs
  have hg : HasSum g t := ht
  have hprod : Summable (fun ij : ℕ × ℕ => f ij.1 * g ij.2) :=
    hf.summable.mul_of_nonneg hg.summable
      (fun n => mul_nonneg (hP n) (pow_nonneg hr n))
      (fun n => mul_nonneg (hQ n) (pow_nonneg hr n))
  have hsum : Summable (fun n : ℕ =>
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  have heq := hf.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.summable hprod
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  have hconv : HasSum (fun n : ℕ =>
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) (s * t) := by
    rw [heq]
    exact hsum.hasSum
  have hcoeff : (fun n : ℕ =>
      ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) =
      (fun n : ℕ => PowerSeries.coeff n (P * Q) * r ^ n) := by
    funext n
    exact bennett_positive_weighted_coeff_mul P Q r n
  rw [← hcoeff]
  exact hconv





end D1Bound5
end
