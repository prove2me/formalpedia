-- Prove2me | solution 1 for D1Bound5.bennettClearedTaylor_two_poles_weighted_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:26.074994+00:00
-- url     : https://prove2.me/submissions/ee1147ad-1684-46b8-88bb-68d1b8282c4e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettCoefficientMajorant_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettPositiveSeries_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_eval_norm_le_coeff
import Theorems.Thm_D1Bound5_bennettNumeratorMajorant_hasSum
import Theorems.Thm_D1Bound5_bennettPoleMajorant_coeff
import Theorems.Thm_D1Bound5_bennettPoleMajorant_hasSum
import Theorems.Thm_D1Bound5_bennettPoleSeries_coeff
import Theorems.Thm_D1Bound5_bennettSeries_coeff_C_add_X_pow
import Theorems.Thm_D1Bound5_bennett_coeff_mul_norm_le
import Theorems.Thm_D1Bound5_bennett_positive_series_mul_hasSum

section
open Finset

namespace D1Bound5











theorem bennettNumeratorMajorant_coeff_nonneg (U : ℝ) (hU : 0 < U) (k h : ℕ) :
    0 ≤ PowerSeries.coeff h (bennettNumeratorMajorant U k) := by
  rw [bennettNumeratorMajorant, PowerSeries.coeff_C_mul,
    bennettSeries_coeff_C_add_X_pow]
  positivity





end D1Bound5
end

section
open Finset

namespace D1Bound5





theorem bennettPoleMajorant_coeff_nonneg (d : ℝ) (hd : 0 ≤ d) (p n : ℕ) :
    0 ≤ PowerSeries.coeff n (bennettPoleMajorant d p) := by
  rw [bennettPoleMajorant_coeff]
  exact mul_nonneg (abs_nonneg _) (pow_nonneg (inv_nonneg.mpr hd) _)

/-- The majorant coefficients equal the norms of the actual complex pole
series coefficients, with exactly the same pole order and displacement. -/
theorem bennettPoleSeries_coeff_norm_eq_majorant (z : ℂ) (p n : ℕ) :
    ‖PowerSeries.coeff n (bennettPoleSeries z p)‖ =
      PowerSeries.coeff n (bennettPoleMajorant ‖z‖ p) := by
  have hcast : Ring.choose (-(p : ℂ)) n = Complex.ofReal (Ring.choose (-(p : ℝ)) n) := by
    simpa using (Ring.map_choose (algebraMap ℝ ℂ) (-(p : ℝ)) n).symm
  rw [bennettPoleSeries_coeff, norm_mul, norm_pow, norm_inv,
    bennettPoleMajorant_coeff, hcast, Complex.norm_real, Real.norm_eq_abs]



/-- Multiplying two series with nonnegative coefficients preserves
coefficient nonnegativity. -/
theorem bennett_positive_coeff_mul
    (P Q : PowerSeries ℝ)
    (hP : ∀ n, 0 ≤ PowerSeries.coeff n P)
    (hQ : ∀ n, 0 ≤ PowerSeries.coeff n Q) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (P*Q) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hP ij.1) (hQ ij.2))





/-- Every nonnegative weighted coefficient is bounded by the actual sum. -/
theorem bennett_positive_series_coeff_le_sum
    (P : PowerSeries ℝ) (r s : ℝ) (hr : 0 ≤ r)
    (hP : ∀ n, 0 ≤ PowerSeries.coeff n P)
    (hs : HasSum (fun n : ℕ => PowerSeries.coeff n P * r^n) s) (n : ℕ) :
    PowerSeries.coeff n P * r^n ≤ s := by
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum n
    (fun m _ => mul_nonneg (hP m) (pow_nonneg hr m))



end D1Bound5
end

section
namespace D1Bound5

/-- A genuine two-pole local Taylor coefficient is bounded by the positive
generating-function majorant. No Cauchy coefficient estimate is assumed. -/
theorem _root_.solution
    (a N d e : ℂ) (k t p q : ℕ) (ht : t ≤ k)
    (r : ℝ) (hr : 0 ≤ r) (hU : 0 < ‖N + a‖)
    (hd : r < ‖d‖) (he : r < ‖e‖) :
    ‖(bennettClearedTaylor k t (1 / 2 : ℂ) a
      (bennettPoleSeries d p * bennettPoleSeries e q)).eval N‖ * r ^ t ≤
      ((‖N + a‖ + r) ^ (k + 1) / ‖N + a‖) *
        ((‖d‖ - r)⁻¹ ^ p * (‖e‖ - r)⁻¹ ^ q) := by
  let P := bennettNumeratorMajorant ‖N + a‖ k
  let D := bennettPoleMajorant ‖d‖ p
  let E := bennettPoleMajorant ‖e‖ q
  have hP := bennettNumeratorMajorant_coeff_nonneg ‖N + a‖ hU k
  have hD := bennettPoleMajorant_coeff_nonneg ‖d‖ (norm_nonneg d) p
  have hE := bennettPoleMajorant_coeff_nonneg ‖e‖ (norm_nonneg e) q
  have hDE := bennett_positive_coeff_mul D E hD hE
  have hnorm : ∀ h, ‖PowerSeries.coeff h (bennettPoleSeries d p * bennettPoleSeries e q)‖ ≤
      PowerSeries.coeff h (D * E) := by
    apply bennett_coeff_mul_norm_le
    · intro h
      exact (bennettPoleSeries_coeff_norm_eq_majorant d p h).le
    · intro h
      exact (bennettPoleSeries_coeff_norm_eq_majorant e q h).le
  have hc := bennettClearedTaylor_eval_norm_le_coeff k t ht a N _ (D * E) hU hnorm
  have hsumDE := bennett_positive_series_mul_hasSum D E r
    ((‖d‖ - r)⁻¹ ^ p) ((‖e‖ - r)⁻¹ ^ q) hr hD hE
    (bennettPoleMajorant_hasSum ‖d‖ r p (hr.trans_lt hd) hr hd)
    (bennettPoleMajorant_hasSum ‖e‖ r q (hr.trans_lt he) hr he)
  have hsum := bennett_positive_series_mul_hasSum P (D * E) r
    ((‖N + a‖ + r) ^ (k + 1) / ‖N + a‖)
    ((‖d‖ - r)⁻¹ ^ p * (‖e‖ - r)⁻¹ ^ q) hr hP hDE
    (bennettNumeratorMajorant_hasSum ‖N + a‖ r k) hsumDE
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg hr _)).trans
    (bennett_positive_series_coeff_le_sum (P * (D * E)) r _ hr
      (bennett_positive_coeff_mul P (D * E) hP hDE) hsum t)



end D1Bound5
end
