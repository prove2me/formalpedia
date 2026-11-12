-- Prove2me | solution 1 for Erdos970.Complex.Hadamard.hadamardQuotient_norm_le_exp_on_cartan_circle_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:46:05.924071+00:00
-- url     : https://prove2.me/submissions/c7169130-e12b-4070-b040-98e9f17542ab

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J000

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_SpecialFunctions_Log_PosLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Positive-log estimates

Small estimates for `Real.log⁺` and for converting logarithmic growth bounds into exponential
bounds.
-/


namespace Real

/-- Lower bound for `log x` in terms of `log⁺ x⁻¹`. -/
theorem neg_posLog_inv_le_log (x : ℝ) : -log⁺ x⁻¹ ≤ log x := by
  linarith [posLog_sub_posLog_inv (x := x), posLog_nonneg (x := x)]

end Real
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_CartanBound
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-!
# Cartan bounds for Hadamard factorization

Probabilistic-radius and averaging lemmas for the minimum-modulus step in the intrinsic Hadamard
pipeline. The basic pointwise input is

`log⁺ (1 / |1 - t|) ≤ √(2 / |1 - t|)`,

which majorizes the logarithmic singularity on dyadic intervals.

## References

* [tao246bComplexAnalysis] for the disk and averaging viewpoint
* [MR886677] for disk automorphisms and canonical factors on the unit disk
* [boas1954] and [levin1980] for the minimum-modulus estimates used in Hadamard factorization
-/


namespace Complex
namespace CartanBound

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal

/-!
### Pointwise bound for the logarithmic singularity

Used as an integrable majorant when averaging `log⁺ (1 / |1 - t|)` on dyadic intervals.
-/

/-! ### A radial majorant for the logarithmic singularity on a circle -/

/-! ### A coarse dyadic-interval bound for the singularity average -/

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by
  simpa [φ] using (Real.posLog_nonneg (x := (1 / |1 - t|)))


/-!
### Bridge lemma: from the 1D singularity `φ` to a complex lower bound

On a circle `‖u‖ = r`, the quantity `log ‖1 - u/a‖` is bounded below in terms of `φ(r/‖a‖)`.
This is the local estimate in the probabilistic-radius argument.
-/

lemma log_norm_one_sub_div_ge_neg_phi {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -φ (r / ‖a‖) := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have hnorm_ge : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [habs]
      exact hdiv
    rwa [hnorm_eq]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have hlogx :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖) := by
    have := Real.neg_posLog_inv_le_log (x := |1 - (r / ‖a‖)|)
    simpa [φ, one_div, inv_inv, abs_sub_comm, sub_eq_add_neg] using this
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) hnorm_ge
  linarith [hlog_mono, hlogx]

lemma K_nonneg : 0 ≤ K := by
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro _t _ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg
    (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)

lemma Cφ_pos : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := K_nonneg
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this

/-!
### A “good radius” lemma (probabilistic-radius / Cartan averaging)

This is the abstract selection principle used in the dyadic averaging: if an averaged singularity
kernel has controlled integral on `[R,2R]`, then there exists a radius `r ∈ (R,2R]` where the
pointwise sum is controlled.
-/

open scoped BigOperators

end CartanBound
end Complex
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_Norm
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Norm estimates for complex analysis

Elementary norm estimates used in Cartan-style product bounds and Gamma/zeta growth arguments.
-/


noncomputable section

namespace Complex

variable {z : ℂ}

/-- If `‖u‖ ≥ 1`, then inverse powers of `u` have norm at most one. -/
lemma norm_inv_pow_le_one_of_one_le_norm (u : ℂ) (n : ℕ) (hu : (1 : ℝ) ≤ ‖u‖) :
    ‖(u ^ n)⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖u ^ n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u ^ n)⁻¹‖ = ‖(1 : ℂ) / u ^ n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u ^ n‖ := by
        have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
        rw [Complex.norm_div, hone]
    _ ≤ 1 := by simpa [one_div] using inv_le_one_of_one_le₀ hge

end Complex
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_SpecialFunctions_Complex_LogBounds
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Logarithm estimates for Weierstrass products

This file develops the finite truncation and tail estimates for the logarithm series
`-log (1 - z)`.  These estimates are the local analytic input for bounding Weierstrass
factors and canonical products.
-/


open scoped BigOperators

namespace Real

/-- If `0 ≤ r ≤ 1 / 2`, then the geometric-factor denominator is bounded by `2`. -/
lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring

end Real

namespace Complex

open scoped BigOperators in
/-- On the open unit disk, `-log (1 - z)` is the `tsum` with index shift `n ↦ n + 1`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel

/-- Evaluate `logTaylor` at `-z` as a finite positive-coefficient logarithm sum. -/
lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf

/-- `partialLogSum` is the partial sum `∑_{k=1}^m z^k / k`. -/
lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)

lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)

lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt

lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

/-- A coarse geometric-series bound for the logarithm tail. This intentionally drops the
extra denominator `m + 1 + k`; the weaker estimate is the form used by the Weierstrass-factor
bounds below. -/
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [logTail]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)

lemma norm_partialLogSum_le_nat_mul_max_one_norm_pow (m : ℕ) (z : ℂ) :
    ‖partialLogSum m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  have hsum :
      ‖partialLogSum m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
    rw [partialLogSum_eq_sum]
    exact norm_sum_le _ _
  have hterm : ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
    intro k hk
    rw [norm_div, norm_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast hk1_nat
    have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (k + 1))
    have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have hpow_le : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
      · have : ‖z‖ ^ (k + 1) ≤ 1 := by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := pow_le_pow_right₀ hz1' hk_le
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
      _ ≤ ‖z‖ ^ (k + 1) := by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m) := hpow_le
  have hsum_le :
      (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖) ≤
        ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hcard : ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) = (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simp [Finset.sum_const]
  exact hsum.trans (hsum_le.trans_eq hcard)

/-- Decompose the logarithm series into its first `m` terms and the remaining tail. -/
lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf

end Complex
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_WeierstrassFactor
attribute [-simp] _root_.Complex.canonicalProduct_def _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Weierstrass elementary factors

We define the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (as `Complex.weierstrassFactor`) and prove basic
properties and estimates

## Main definitions

* `Complex.partialLogSum m z`: the truncation of `-log (1 - z)`, defined via `Complex.logTaylor`
* `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` as a `tsum` starting at `m + 1`
* `Complex.weierstrassFactor m z`: the elementary factor `E_m(z)`

## Main results

* `Complex.weierstrassFactor_sub_one_pow_bound`: `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`
* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-logTail m z)`
* `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow`: a crude bound on the truncated
  logarithm series
* `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow`: a crude lower
  bound for `log ‖E_m(z)‖` used in minimum-modulus arguments
-/


noncomputable section

open scoped BigOperators
open Set

namespace Complex

/-! ## The Weierstrass factor -/

lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [weierstrassFactor] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [weierstrassFactor]

lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))

/-- For `‖z‖ < 1` and `z ≠ 1`, `E_m(z) = exp(-logTail_m(z))`. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]

/-! ## Power bound -/

/-- For `‖z‖ ≤ 1 / 2`, `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)`. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

/-!
## Lower bounds on `Real.log ‖weierstrassFactor m z‖`

Auxiliary inequalities for minimum-modulus / Cartan-type arguments in Hadamard factorization.
-/

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - ‖partialLogSum m z‖ ≤ Real.log ‖weierstrassFactor m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [weierstrassFactor]
  set S : ℂ := partialLogSum m z
  have hS : weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
              simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.neg_norm_le_re S
  have : Real.log ‖weierstrassFactor m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  simpa [S] using this

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    simpa [norm_neg] using Complex.neg_norm_le_re (-logTail m z)
  have htail := norm_logTail_le_two_mul_norm_pow hz_lt hz m
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

/-! ## Locally uniform convergence of products of scaled factors -/

end Complex
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_CartanInverseFactorBound
attribute [-simp] _root_.Complex.canonicalProduct_def _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-!
## Pointwise inverse bounds for Weierstrass factors in Cartan-type arguments

This file bundles two pointwise estimates used in Cartan/minimum-modulus arguments for Hadamard
factorization:

- a bound in the “near regime”, combining `Complex.CartanBound.log_norm_one_sub_div_ge_neg_phi` with
  the general lower bound `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_sub`;
- a bound in the “far regime” (`‖u / a‖ ≤ 1 / 2`), based on
  `Complex.log_norm_weierstrassFactor_ge_neg_two_pow`.

The results are stated in a form convenient for divisor-indexed zero enumerations.
-/


noncomputable section

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

open Complex _root_.Real

/-!
### Auxiliary: bound `max 1 (‖u/a‖^m)` by `1 + (r/‖a‖)^τ`

This is the small “exponent comparison” lemma that occurs everywhere in the near regime.
-/

lemma max_one_norm_div_pow_le_one_add_rpow
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r)
    (hmτ : (m : ℝ) ≤ τ) :
    max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
  by_cases hx : ‖u / a‖ ≤ 1
  · have hpowm_le1 : ‖u / a‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg (u / a)) hx
    have hr0 : 0 ≤ r := by simpa [hur] using (norm_nonneg u)
    have hbase : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have hnonneg : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg hbase τ
    have hle1 : (1 : ℝ) ≤ 1 + (r / ‖a‖) ^ τ := le_add_of_nonneg_right hnonneg
    have hle2 : ‖u / a‖ ^ m ≤ 1 + (r / ‖a‖) ^ τ := hpowm_le1.trans hle1
    exact (max_le_iff).2 ⟨hle1, hle2⟩
  · have hx1 : 1 < ‖u / a‖ := lt_of_not_ge hx
    have hpow :
        (‖u / a‖ : ℝ) ^ (m : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hmτ
    have hpow' : ‖u / a‖ ^ m ≤ (‖u / a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using hpow
    have hmax_add : max 1 (‖u / a‖ ^ m) ≤ 1 + ‖u / a‖ ^ m := by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u / a‖ ^ m) ≤ 1 + (‖u / a‖ : ℝ) ^ τ :=
      hmax_add.trans (by nlinarith [hpow'])
    simpa [norm_div, hur] using this

/-!
### Near regime: `‖(E_m(u/a))⁻¹‖` controlled by `φ(r/‖a‖)` plus an exponent term.
-/

lemma norm_inv_weierstrassFactor_le_exp_near
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
    (hmτ : (m : ℝ) ≤ τ) :
    ‖(weierstrassFactor m (u / a))⁻¹‖
      ≤ Real.exp (CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
  have hlog_one :
      Real.log ‖(1 : ℂ) - u / a‖ ≥ -CartanBound.φ (r / ‖a‖) :=
    CartanBound.log_norm_one_sub_div_ge_neg_phi (hur := hur) (ha := ha) (hr := hr)
  have hbase :=
    log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m := m) (z := (u / a))
  have hlogE :
      Real.log ‖weierstrassFactor m (u / a)‖
        ≥ -CartanBound.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
    have hpls :=
      norm_partialLogSum_le_nat_mul_max_one_norm_pow m (u / a)
    linarith [hbase, hlog_one, hpls]
  have hmax :
      max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ :=
    max_one_norm_div_pow_le_one_add_rpow (m := m) (τ := τ) (r := r) (u := u) (a := a) hur hmτ
  have hneglog :
      -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
    have : -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      linarith [hlogE]
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : r = ‖a‖ := by simpa [this] using hur.symm
      exact (hr this).elim
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

/-!
### Far regime: if `‖u/a‖ ≤ 1/2` then `‖(E_m(u/a))⁻¹‖ ≤ exp(2*(r/‖a‖)^τ)`
-/

lemma norm_inv_weierstrassFactor_le_exp_far
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0)
    (hz : ‖u / a‖ ≤ (1 / 2 : ℝ)) (hτ_le : τ ≤ (m + 1 : ℝ)) :
    ‖(weierstrassFactor m (u / a))⁻¹‖ ≤ Real.exp ((2 : ℝ) * (r / ‖a‖) ^ τ) := by
  by_cases hu : u = 0
  · subst hu
    have hr0 : r = 0 := by simpa [hur] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0 : ℝ) / ‖a‖) ^ τ := by
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have hexp : (1 : ℝ) ≤ Real.exp ((2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using hexp
  have hlogE :=
    log_norm_weierstrassFactor_ge_neg_two_pow (m := m) (z := (u / a)) hz
  have hneglog : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * (r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * ‖u / a‖ ^ (m + 1) := by
      linarith [hlogE]
    set x : ℝ := ‖u / a‖
    have hx1 : x ≤ 1 := le_trans (by simpa [x] using hz) (by norm_num)
    have hxpos : 0 < x := by
      simpa [x] using (norm_pos_iff.2 (div_ne_zero hu ha))
    have hτ_le' : τ ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hτ_le
    have hpow_rpow : x ^ ((m + 1 : ℕ) : ℝ) ≤ x ^ τ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hτ_le'
    have hpow : x ^ (m + 1) ≤ x ^ τ := by
      simpa [← Real.rpow_natCast] using hpow_rpow
    have h2x : (2 : ℝ) * x ^ (m + 1) ≤ (2 : ℝ) * x ^ τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h2 : (2 : ℝ) * ‖u / a‖ ^ (m + 1) ≤ (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ := by
      simpa [x] using h2x
    have h3 : (‖u‖ / ‖a‖) ^ τ = (r / ‖a‖) ^ τ := by
      simp [hur]
    exact (h1.trans h2).trans_eq (by simp [h3])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : (‖u / a‖ : ℝ) = 1 := by simpa [this] using (by simp [ha])
      linarith [hz, this]
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

end Complex.Hadamard
end Erdos970
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorConvergence
attribute [-simp] _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_one_of_mem _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-!
# Convergence and holomorphy of divisor-indexed canonical products

This file proves uniform convergence on compacts, locally uniform convergence, holomorphy, and the
genus-one logarithmic-derivative identity for the divisor-indexed canonical product
`Complex.Hadamard.divisorCanonicalProduct`, under the standard summability hypothesis.

It also provides finiteness lemmas for subsets of the divisor index type cut out by a norm bound.
-/


open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Finiteness of “small” divisor indices
-/

/-!
## Uniform convergence on compact sets
-/

lemma norm_div_le_half_of_norm_le_of_two_mul_lt {z a : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2 * R : ℝ) < ‖a‖) :
    ‖z / a‖ ≤ (1 / 2 : ℝ) := by
  have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hR]
  have hinv : ‖a‖⁻¹ < (2 * R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt h2R_pos ha
  have hmul_le : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have hmul_lt : R * ‖a‖⁻¹ < R * (2 * R)⁻¹ :=
    mul_lt_mul_of_pos_left hinv hR
  have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
    have hRne : (R : ℝ) ≠ 0 := hR.ne'
    rw [show R * (2 * R)⁻¹ = R / (2 * R) by simp [div_eq_mul_inv]]
    field_simp [hRne]
  have hnorm : ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := hnorm
      _ ≤ R * ‖a‖⁻¹ := hmul_le
      _ < R * (2 * R)⁻¹ := hmul_lt
      _ = (1 / 2 : ℝ) := hRhalf

theorem hasProdUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ)) K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} :
            Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    have hzle : ‖z‖ ≤ R := hnormK z hzK
    have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      exact norm_div_le_half_of_norm_le_of_two_mul_lt hRpos hzle hp
    have hE :
        ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
      gcongr
    dsimp [g, u]
    nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
      (differentiable_weierstrassFactor m).continuous
    have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
      simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
    have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
      hcontE.comp hdiv
    simpa only [g] using hcont.continuousOn.fun_sub continuous_const.continuousOn
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  simpa [g, divisorCanonicalProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using! hprod

/-!
## Entire-ness (holomorphy) of the divisor-indexed canonical product
-/

theorem hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (g := divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (s := (Set.univ : Set ℂ)) isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) (K := K) hK h_sum)

/-!
## Logarithmic derivative of the genus-one divisor product
-/

end Complex.Hadamard
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_DivisorFiber
attribute [-simp] _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_one_of_mem _root_.Erdos970.Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem _root_.Erdos970.Complex.Hadamard.divisorComplementPartialProduct_def _root_.Erdos970.Complex.Hadamard.divisorPartialProduct_def _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-!
# Fibers of the divisor index type

This file studies the fiber `{p : divisorZeroIndex₀ f univ | divisorZeroIndex₀_val p = z₀}`.
It provides a canonical `Finset` for this fiber and identifies its cardinality with the divisor
multiplicity and (for holomorphic functions) with `analyticOrderNatAt`.
-/


noncomputable section

open Set
open scoped Topology BigOperators

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-!
## Divisor values vs analytic order (holomorphic functions)
-/

lemma divisor_univ_eq_analyticOrderNatAt_int {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
  have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro w hw
    exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
  simp only
    [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)), analyticOrderNatAt]
  have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
  cases h : analyticOrderAt f z with
  | top =>
      simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
      simp [han.meromorphicOrderAt_eq, h]

/-!
## The multiplicity fiber is finite and has the expected cardinality
-/

lemma divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | divisorZeroIndex₀_val p = z₀}
  have hS : S.Finite := divisorZeroIndex₀_fiber_finite (f := f) z₀
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    have : Fintype S := hS.fintype
    -- `S` is the fiber over `z₀`, hence equivalent to `Fin (Int.toNat (divisor z₀))`.
    let e : S ≃ Fin n :=
      { toFun := by
          intro x
          rcases x with ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using! hp
          subst hzEq
          simpa [n] using q
        invFun := by
          intro q
          refine ⟨⟨⟨z₀, ?_⟩, hz₀⟩, ?_⟩
          · simpa [n] using q
          · simp [S, divisorZeroIndex₀_val]
        left_inv := by
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using! hp
          subst hzEq
          (ext; rfl)
        right_inv := by
          intro q
          rfl }
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have hSncard : S.ncard = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  have hto : hS.toFinset = divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    rfl
  have htoFinset : S.ncard = (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact htoFinset.symm.trans hSncard

lemma divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ := by
  have hdiv :
      MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
    divisor_univ_eq_analyticOrderNatAt_int (f := f) hf z₀
  have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
    analyticOrderNatAt f z₀ := by
    simp [hdiv]
  exact (divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f := f) (z₀ := z₀) hz₀).trans htoNat

end Complex.Hadamard
end Erdos970
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_Divisor
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-!
# Hadamard factorization (preliminaries)

This file develops preliminary lemmas towards Hadamard factorization for entire functions on `ℂ`.
Zeros are indexed with multiplicity using `MeromorphicOn.divisor`, then assembled into the
corresponding canonical product.

## Main definitions

- `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types enumerating
  zeros with multiplicity.
- `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.
- `Complex.Hadamard.divisorComplementCanonicalProduct`: the canonical product with the fiber over a
  fixed point `z₀` removed.

## Main results

- The support of the divisor is discrete and countable, and meets compact sets in finitely many
  points.
- Under the standard summability hypothesis, the canonical product converges uniformly on compact
  sets, and its analytic order agrees with the expected multiplicity away from `0`.
-/


namespace Erdos970.Complex
namespace Hadamard
open _root_.Complex

/-!
## Nonvanishing helpers for Weierstrass factors
-/

open scoped Topology
open _root_.Set

/-!
## Local finiteness on compact sets

For `D : Function.locallyFinsuppWithin U ℤ`, the support is *locally finite within `U`*.
Hence any compact `K ⊆ U` meets `D.support` only finitely often.

This yields “eventually in `cofinite`” bounds for divisor-indexed products.
-/

/-!
## Entire functions are never locally zero (under a global nontriviality witness)

If `f` is differentiable on `ℂ` and not identically zero, then it is not locally zero anywhere,
hence `analyticOrderAt f z ≠ ⊤` for all `z`.
-/

lemma analyticOrderAt_ne_top_of_exists_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top

/-!
## Avoiding zeros on a circle

If `f` is entire and not identically zero, and if a radius `r > 0` is different from the norms of
all (nonzero) divisor-indexed zeros inside an ambient bound `B`, then `f` has no zeros on the circle
`‖z‖ = r`.
-/

lemma no_zero_on_sphere_of_forall_val_norm_ne
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hBr : r ≤ B) (hr_not : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      ‖divisorZeroIndex₀_val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀_val p‖) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  intro u hur
  have hu0 : u ≠ 0 := by
    intro hu0
    subst hu0
    have : (0 : ℝ) = r := by simpa using hur
    exact (ne_of_gt hrpos) this.symm
  intro hfu0
  have hnotTop : analyticOrderAt f u ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (f := f) hf hnot u
  have hord_ne0 : analyticOrderNatAt f u ≠ 0 := by
    intro h0
    have hEN : (analyticOrderNatAt f u : ENat) = 0 := by simp [h0]
    have hAt0 : analyticOrderAt f u = 0 := by
      have hcast : (analyticOrderNatAt f u : ENat) = analyticOrderAt f u :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := u) hnotTop
      simpa [hcast] using hEN
    have han : AnalyticAt ℂ f u := Differentiable.analyticAt (f := f) hf u
    exact ((han.analyticOrderAt_eq_zero).1 hAt0) hfu0
  have hcard_pos : 0 < (divisorZeroIndex₀_fiberFinset (f := f) u).card := by
    have hcard :=
      divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := u) hu0
    have : 0 < analyticOrderNatAt f u := Nat.pos_of_ne_zero hord_ne0
    simpa [hcard] using this
  rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
  have hpval : divisorZeroIndex₀_val p = u :=
    (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := u) p).1 hp
  have hpB : ‖divisorZeroIndex₀_val p‖ ≤ B := by
    have : ‖divisorZeroIndex₀_val p‖ = r := by simp [hpval, hur]
    simpa [this] using hBr
  have : r ≠ ‖divisorZeroIndex₀_val p‖ := hr_not p hpB
  exact this (by simp [hpval, hur])

/-!
## The divisor canonical product vanishes at indexed zeros

If one of the factors is `0` at `z`, then the infinite product is `0`.
-/

/-!
## The fiber finite product has the expected order at `z₀`

This packages the finite multiplicity calculation for the specific finset corresponding to the fiber
`{p | divisorZeroIndex₀_val p = z₀}`.
-/

/-!
## Exact multiplicity of the divisor canonical product

The infinite canonical product has precisely the zero multiplicities encoded by the divisor index.
The proof is supplied by the quotient/removable-singularity layer, and the
statements here record the multiplicity theorem at the level where the product is introduced.
-/

/-!
## Refining the factorization: factoring out `(z - z₀)^k` using the fiber-only product

When `s` contains the fiber finset, we can write the partial product as

`divisorPartialProduct s = (z - z₀)^k • (divisorComplementPartialProduct s * u)`

where `u` is the analytic quotient coming from the fiber-only product.
-/


end Hadamard
end Complex
end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_CartanMajorantBound
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
## Cartan bookkeeping: bound finite sums of the majorant

This file isolates the finite-sum estimate used in the Cartan/minimum-modulus argument:
we bound finite partial sums `∑_{p∈s} b p` of the majorant exponent `b` by
`Cprod * (1+r)^τ`, where `Cprod` depends only on `τ`, `m`, and the τ-sum `Sτ`.
-/


noncomputable section

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

open scoped BigOperators
open _root_.Filter _root_.Finset _root_.Real Topology

section CartanFiniteSum

variable {α : Type*}

/-- A function supported on a finite set is summable. -/
private lemma summable_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    Summable (fun a => if a ∈ s then u a else 0) :=
  summable_of_ne_finset_zero (s := s) fun a ha => by simp [if_neg ha]

/-- The tsum of a finset-supported function is the finset sum. -/
private lemma tsum_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    (∑' a, if a ∈ s then u a else 0) = ∑ a ∈ s, u a := by
  classical
  simpa [Finset.sum_ite] using
    (hasSum_sum_of_ne_finset_zero (s := s) (f := fun a => if a ∈ s then u a else 0)
      fun a ha => by simp [if_neg ha]).tsum_eq

/-- Split a tsum of four summable summands. -/
private lemma tsum_add_four (u₁ u₂ u₃ u₄ : α → ℝ)
    (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) :
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
      = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  calc
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
        = tsum (fun a => (u₁ a + u₂ a) + (u₃ a + u₄ a)) := by
          simp [add_comm, add_left_comm]
    _ = tsum (fun a => u₁ a + u₂ a) + tsum (fun a => u₃ a + u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [Summable.tsum_add h₁ h₂, Summable.tsum_add h₃ h₄]
        ring

end CartanFiniteSum

lemma rpow_div_norm_divisorZeroIndex₀_eq
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    (r / ‖divisorZeroIndex₀_val p‖) ^ τ =
      (r ^ τ) * ((‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) := by
  have hp : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ)) (z := τ) hr hp)

lemma tsum_rpow_div_norm_divisorZeroIndex₀_eq
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) :
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
      = (r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
  calc
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
        = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
            (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
            refine tsum_congr ?_
            intro p
            exact rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p
    _ = (r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
        simp [tsum_mul_left]

lemma tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (2 : ℝ) * (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
      ≤ (2 : ℝ) * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have htsum :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
        = (2 : ℝ) * (r ^ τ) * Sτ := by
    calc
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
          = (2 : ℝ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
              (r / ‖divisorZeroIndex₀_val p‖) ^ τ := by
              simp [tsum_mul_left]
      _ = (2 : ℝ) * ((r ^ τ) * Sτ) := by
              rw [tsum_rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr]
      _ = (2 : ℝ) * (r ^ τ) * Sτ := by ring
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : Sτ ≤ Sτ + 1 := by linarith
  have hle : (r ^ τ) * Sτ ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by linarith) (by positivity)
  rw [htsum]
  have : (2 : ℝ) * (r ^ τ) * Sτ ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
    nlinarith [hle]
  simpa [Sτ, mul_assoc, mul_left_comm, mul_comm] using this

lemma sum_rpow_div_norm_divisorZeroIndex₀_le
    {f : ℂ → ℂ} {r τ : ℝ} (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ)
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    (∑ p ∈ small, (r / ‖divisorZeroIndex₀_val p‖) ^ τ)
      ≤ ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hsum_inv :
      (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ := by
    have hnn : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
      intro p
      positivity
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hsum_eq :
      ∑ p ∈ small, (r / ‖divisorZeroIndex₀_val p‖) ^ τ =
        (r ^ τ) * ∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
    simp [rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr, Finset.mul_sum]
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ + 1 := by
    linarith [hsum_inv]
  have hle :
      (r ^ τ) * (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)
        ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by positivity) (by positivity)
  simpa [Sτ, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hle

lemma add_four_le_add_two_mul_of_le {x₁ x₂ x₃ x₄ A B C : ℝ}
    (h₁ : x₁ ≤ A) (h₂ : x₂ ≤ B) (h₃ : x₃ ≤ B) (h₄ : x₄ ≤ C) :
    x₁ + x₂ + x₃ + x₄ ≤ A + 2 * B + C := by
  nlinarith

lemma cartan_majorant_four_term_bound
    {xφ x0 xm xt Cφ m q Y T : ℝ}
    (hφ : xφ ≤ Cφ * q * Y * T)
    (h0 : x0 ≤ m * q * Y * T)
    (hm : xm ≤ m * q * Y * T)
    (ht : xt ≤ (2 : ℝ) * Y * T) :
    xφ + x0 + xm + xt ≤ (Cφ + (2 : ℝ) * m) * q * Y * T + (2 : ℝ) * Y * T := by
  have h :=
    add_four_le_add_two_mul_of_le hφ h0 hm ht
  have hring :
      Cφ * (q * (Y * T)) + 2 * (m * (q * (Y * T))) + 2 * (Y * T)
        = (Cφ + (2 : ℝ) * m) * (q * (Y * T)) + (2 : ℝ) * (Y * T) := by
    ring
  simpa [mul_assoc, hring] using h

lemma cartan_majorant_add_two_factor (A Y T : ℝ) :
    A * Y * T + (2 : ℝ) * Y * T = ((A + 2) * Y) * T := by
  ring

lemma cartan_majorant_pad_two_to_three {A S T : ℝ} (hS : 0 ≤ S + 1) (hT : 0 ≤ T) :
    ((A + 2) * (S + 1)) * T ≤ ((A + 3) * (S + 1)) * T := by
  have h : (A + 2) * (S + 1) ≤ (A + 3) * (S + 1) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right h hT

lemma cartan_majorant_nonneg
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    ∀ p, 0 ≤ b p := by
  classical
  dsimp
  intro p
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀_val q‖
  have hap : ap p = ‖divisorZeroIndex₀_val p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ CartanBound.φ (r / ap p) := CartanBound.φ_nonneg (t := r / ap p)
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1 + (r / ap p) ^ τ) := by positivity
    have : 0 ≤ CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ) := by
      nlinarith [hφ, hm0, h1]
    simpa [hap, hp, ap] using this
  · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
    have hpow : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
    have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hpow
    simpa [hap, hp, ap] using this

lemma cartan_majorant_summable
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    Summable b := by
  classical
  dsimp
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀_val q‖
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hb : Summable b := by
    let b₁ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else 0
    let b₂ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2 : ℝ) * (r / ap p) ^ τ
    have hb_decomp : b = fun p => b₁ p + b₂ p := by
      funext p
      by_cases hp : p ∈ small <;> simp [b, b₁, b₂, hp]
    have hb₁ : Summable b₁ := by
      simpa [b₁] using
        summable_ite_mem_finset small
          (fun p => CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ))
    have hb₂ : Summable b₂ := by
      have hconst :
          Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :=
        hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂, hp]
          · have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := by positivity
            simpa [b₂, hp] using this)
        (fun p => ?_) hconst
      by_cases hp : p ∈ small
      · have : 0 ≤ (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by positivity
        simpa [b₂, hp] using this
      · have hrpow : (r / ap p) ^ τ = (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
          simpa [ap] using rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p
        simp [b₂, hp, hrpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [hb_decomp] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b, ap, hp]

lemma cartan_card_small_le
    {f : ℂ → ℂ} {τ R : ℝ} (hRpos : 0 < R) (hτ_nonneg : 0 ≤ τ)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall : ∀ p ∈ small, ‖divisorZeroIndex₀_val p‖ ≤ 4 * R)
    (hsumτ :
      Summable
        (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    (small.card : ℝ)
      ≤ (4 * R) ^ τ
          * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
                ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) := by
  classical
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hsum_le : (∑ p ∈ small, ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) ≤ Sτ := by
    have hnn :
        ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          0 ≤ ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
      intro p
      exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hgeom_sum :
      (small.card : ℝ) ≤ ∑ p ∈ small, (4 * R) ^ τ * ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    have hcard_eq : (small.card : ℝ) = ∑ p ∈ small, (1 : ℝ) := by simp
    rw [hcard_eq]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp_le : ‖divisorZeroIndex₀_val p‖ ≤ 4 * R := hsmall p hp
    have hap : 0 < ‖divisorZeroIndex₀_val p‖ :=
      norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
    have hbase : (1 : ℝ) ≤ (4 * R) / ‖divisorZeroIndex₀_val p‖ := by
      exact (le_div_iff₀ hap).2 (by simpa [mul_one] using hp_le)
    have : (1 : ℝ) ≤ ((4 * R) / ‖divisorZeroIndex₀_val p‖) ^ τ :=
      Real.one_le_rpow hbase hτ_nonneg
    have hdiv :
        ((4 * R) / ‖divisorZeroIndex₀_val p‖) ^ τ =
          (4 * R) ^ τ * (‖divisorZeroIndex₀_val p‖)⁻¹ ^ τ := by
      have h4 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
      have ha : 0 ≤ (‖divisorZeroIndex₀_val p‖ : ℝ)⁻¹ := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_rpow (x := (4 * R : ℝ))
          (y := (‖divisorZeroIndex₀_val p‖ : ℝ)⁻¹) (z := τ) h4 ha)
    have : (1 : ℝ) ≤ (4 * R) ^ τ * ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
      simpa [hdiv] using this
    exact this
  have hgeom :
      (small.card : ℝ) ≤ (4 * R) ^ τ * (∑ p ∈ small, ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
    simpa [Finset.mul_sum] using hgeom_sum
  have hsmall_le : (small.card : ℝ) ≤ (4 * R) ^ τ * Sτ := by
    exact hgeom.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hS_le : (4 * R) ^ τ * Sτ ≤ (4 * R) ^ τ * (Sτ + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := hsmall_le.trans hS_le
  simpa [Sτ, add_comm, add_left_comm, add_assoc, mul_assoc] using this

lemma cartan_rpow_mul_le
    {τ R r : ℝ} (hRpos : 0 < R) (hrpos : 0 < r) (hR_le_r : R ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ := by
  have hR_le_1r : R ≤ 1 + r := by linarith [hR_le_r, le_of_lt hrpos]
  have hbase0 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
  have : (4 * R) ^ τ ≤ (4 * (1 + r)) ^ τ := by
    refine Real.rpow_le_rpow hbase0 ?_ hτ_nonneg
    nlinarith [hR_le_1r]
  have hmul : (4 * (1 + r)) ^ τ = (4 : ℝ) ^ τ * (1 + r) ^ τ := by
    have h4 : 0 ≤ (4 : ℝ) := by norm_num
    have h1 : 0 ≤ (1 + r : ℝ) := by positivity
    simpa [mul_assoc] using
      (Real.mul_rpow (x := (4 : ℝ)) (y := (1 + r : ℝ)) (z := τ) h4 h1)
  simpa [hmul] using this

open Classical in
theorem cartan_sum_majorant_le
    {f : ℂ → ℂ} {m : ℕ} {τ R r : ℝ}
    (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hR_le_r : R ≤ r)
    (hτ_nonneg : 0 ≤ τ)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R})
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
    (hr_phi :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
      (∑ p ∈ small, CartanBound.φ (r / a p)) ≤ CartanBound.Cφ * (small.card : ℝ)) :
    let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
      (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
  classical
  intro small ap b Sτ Cprod s
  have hr : 0 ≤ r := le_of_lt hrpos
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have hsmall_mem : ∀ p, p ∈ small ↔ p ∈ smallSet := by
    intro p
    simp [small, hsmall_fin.mem_toFinset]
  have hphi_sum :
      (∑ p ∈ small, CartanBound.φ (r / ap p)) ≤ CartanBound.Cφ * (small.card : ℝ) := by
    simpa [small, ap] using hr_phi
  have hb_nonneg : ∀ p, 0 ≤ b p := by
    simpa [ap, b] using (cartan_majorant_nonneg (f := f) (m := m) (τ := τ) (r := r) hr small)
  have hb_summable : Summable b := by
    simpa [ap, b] using
      (cartan_majorant_summable (f := f) (m := m) (τ := τ) (r := r) hr small hsumτ)
  have hsmall_norm : ∀ p ∈ small, ‖divisorZeroIndex₀_val p‖ ≤ 4 * R := by
    intro p hp
    have : p ∈ smallSet := (hsmall_mem p).1 hp
    simpa [hsmallSet] using this
  have hcard_le : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := by
    simpa [Sτ, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (cartan_card_small_le (f := f) (τ := τ) (R := R) hRpos hτ_nonneg small hsmall_norm hsumτ)
  have hpowR : (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ :=
    cartan_rpow_mul_le (τ := τ) (R := R) (r := r) hRpos hrpos hR_le_r hτ_nonneg
  have hcard_le' : (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
    have : (4 * R) ^ τ * (Sτ + 1) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
      exact mul_le_mul_of_nonneg_right hpowR (by linarith [hSτ_nonneg])
    exact le_trans hcard_le this
  have hb_tsum_le :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) ≤ Cprod * (1 + r) ^ τ := by
    let bφ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then CartanBound.φ (r / ap p) else 0
    let b0 : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) else 0
    let bmτ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) * (r / ap p) ^ τ else 0
    let bt : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2 : ℝ) * (r / ap p) ^ τ
    have hb_pointwise : ∀ p, b p ≤ bφ p + b0 p + bmτ p + bt p := by
      intro p
      by_cases hp : p ∈ small
      · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
        have hx : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
        have hpos : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b, bφ, b0, bmτ, bt, hp]
        nlinarith
      · simp [b, bφ, b0, bmτ, bt, hp]
    have hmaj_summ : Summable (fun p => bφ p + b0 p + bmτ p + bt p) := by
      have hbφ_summ : Summable bφ := by
        simpa [bφ] using summable_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
      have hb0_summ : Summable b0 := by
        simpa [b0] using summable_ite_mem_finset small (fun _ => (m : ℝ))
      have hbmτ_summ : Summable bmτ := by
        simpa [bmτ] using summable_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      have hbt_summ : Summable bt := by
        have hconst : Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :=
          hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
        refine hconst.congr ?_
        intro p
        simp [bt, ap, rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p,
          mul_assoc, mul_left_comm, mul_comm]
      have h' : Summable (fun p => bφ p + b0 p + (bmτ p + bt p)) :=
        (hbφ_summ.add hb0_summ).add (hbmτ_summ.add hbt_summ)
      simpa [add_assoc] using h'
    have htsum_le :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p)
          ≤ ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p) :=
      (hasSum_le hb_pointwise hb_summable.hasSum hmaj_summ.hasSum)
    have htsum_bφ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
          = ∑ p ∈ small, CartanBound.φ (r / ap p) := by
      classical
      simpa [bφ] using tsum_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
    have htsum_b0 :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
          = (m : ℝ) * (small.card : ℝ) := by
      classical
      have : (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) = ∑ p ∈ small, (m : ℝ) := by
        simpa [b0] using tsum_ite_mem_finset small (fun _ => (m : ℝ))
      simp [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have htsum_bmτ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
          = (m : ℝ) * ∑ p ∈ small, (r / ap p) ^ τ := by
      classical
      have :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
            = ∑ p ∈ small, (m : ℝ) * (r / ap p) ^ τ := by
        simpa [bmτ] using tsum_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      simp [this, Finset.mul_sum]
    have htsum_bt :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
          ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
      simpa [bt, ap, Sτ] using
        tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le (f := f) (τ := τ) hr hτ_nonneg
    have hsum_small_rpow_le :
        (∑ p ∈ small, (r / ap p) ^ τ) ≤ (Sτ + 1) * (1 + r) ^ τ := by
      simpa [ap, Sτ] using
        sum_rpow_div_norm_divisorZeroIndex₀_le (f := f) (τ := τ) small hr hτ_nonneg hsumτ
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
    have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
    have htsum_majorant :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
          ≤ (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1))
              * (1 + r) ^ τ := by
      have hφ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
            ≤ CartanBound.Cφ * (small.card : ℝ) := by
        simpa [htsum_bφ] using hphi_sum
      have hb0_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
            ≤ (m : ℝ) * (small.card : ℝ) := by
        simp [htsum_b0]
      have hbmτ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have h0 :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
          have hmul := mul_le_mul_of_nonneg_left hsum_small_rpow_le hm0
          -- `hmul : m * (∑_{p∈small} ...) ≤ m * ((Sτ+1) * (1+r)^τ)`
          simpa [htsum_bmτ, mul_assoc, mul_left_comm, mul_comm] using hmul
        have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) hτ_nonneg
        have hscale :
            (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
          have hnonneg : 0 ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
            have : 0 ≤ (Sτ + 1) * (1 + r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_right h1 hnonneg)
        exact h0.trans hscale
      have hbt_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
            ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htsum_bt
      have hsplit :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, bmτ p) + (∑' p, bt p) := by
        classical
        have hbφ_summ : Summable bφ := by
          simpa [bφ] using summable_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
        have hb0_summ : Summable b0 := by
          simpa [b0] using summable_ite_mem_finset small (fun _ => (m : ℝ))
        have hbmτ_summ : Summable bmτ := by
          simpa [bmτ] using summable_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
        have hbt_summ : Summable bt := by
          have hconst :
              Summable
                (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
                  (2 : ℝ) * (r ^ τ) * ((‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)) :=
            hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
          refine hconst.congr ?_
          intro p
          simp [bt, ap, rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p,
            mul_assoc, mul_left_comm, mul_comm]
        exact tsum_add_four bφ b0 bmτ bt hbφ_summ hb0_summ hbmτ_summ hbt_summ
      have hcard_le'' :
          (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcard_le'
      have hφ_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p) ≤
            CartanBound.Cφ * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : CartanBound.Cφ * (small.card : ℝ) ≤
            CartanBound.Cφ * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hCφ
        exact hφ_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have hb0_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : (m : ℝ) * (small.card : ℝ) ≤ (m : ℝ) * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hm0
        exact hb0_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have htsum_majorant' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        rw [hsplit]
        set Y : ℝ := Sτ + 1 with hY
        set T : ℝ := (1 + r) ^ τ with hT
        have hφ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
              ≤ CartanBound.Cφ * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hφ_le'
        have hb0_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hb0_le'
        have hbmτ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hbmτ_le
        have hbt_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * Y * T := by
          simpa [hY, hT, mul_assoc] using hbt_le
        have hmain :=
          cartan_majorant_four_term_bound
            (q := (4 : ℝ) ^ τ) hφ_leY hb0_leY hbmτ_leY hbt_leY
        simpa [Y, T, add_assoc] using hmain
      have hring :
          (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ
            = (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ := by
        exact cartan_majorant_add_two_factor
          ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ) (Sτ + 1) ((1 + r) ^ τ)
      rw [← hring]
      exact htsum_majorant'
    have hCprod' :
        (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ
          ≤ Cprod * (1 + r) ^ τ := by
      simpa [Cprod, cartanProductConstant, mul_assoc, mul_left_comm, mul_comm] using
        cartan_majorant_pad_two_to_three
          (A := (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ)
          (S := Sτ) (T := (1 + r) ^ τ) hS (by positivity)
    exact (le_trans (le_trans htsum_le htsum_majorant) hCprod')
  have hsum_fin_le :
      (∑ p ∈ s, b p) ≤ (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) := by
    simpa using
      (Summable.sum_le_tsum (s := s) (f := b) (fun p _ => hb_nonneg p) hb_summable)
  exact hsum_fin_le.trans hb_tsum_le

end Complex.Hadamard
end Erdos970
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_CartanProductBound
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false



/-!
## Reusable product bounds by exponentials

This file collects small reusable algebra and infinite-product lemmas:

- bounding finite products by exponentials of finite sums;
- turning a uniform bound on finite partial products into a bound on the `HasProd` limit.
-/


noncomputable section

open scoped BigOperators
open Filter Finset Real Topology

/-!
### Finite products bounded by `exp(sum)`
-/

lemma Finset.prod_le_exp_sum {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm

/-!
### Infinite products: pass a bound on all partial products to the limit
-/

lemma hasProd_le_of_prod_le_exp {α : Type} {f : α → ℝ} {a : ℝ}
    (hf : HasProd f a (SummationFilter.unconditional α))
    {B : ℝ} (hB : ∀ s : Finset α, (∏ x ∈ s, f x) ≤ Real.exp B) :
    a ≤ Real.exp B :=
  hasProd_le_of_prod_le (L := (SummationFilter.unconditional α)) hf hB

lemma hasProd_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, (fac x)⁻¹)
      (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
  have hprod :
      Tendsto (fun s : Finset α => ∏ x ∈ s, fac x)
        (SummationFilter.unconditional α).filter (𝓝 F) := by
    simpa [HasProd] using hfac
  have hinv :
      Tendsto (fun s : Finset α => (∏ x ∈ s, fac x)⁻¹)
        (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
    hprod.inv₀ hF
  refine hinv.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [Finset.prod_inv_distrib]

lemma hasProd_norm_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, ‖(fac x)⁻¹‖)
      (SummationFilter.unconditional α).filter (𝓝 ‖F⁻¹‖)
  have hnorm := (hasProd_inv_unconditional hfac hF).norm
  refine hnorm.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [norm_inv, Finset.prod_inv_distrib]

lemma hasProd_norm_inv_le_exp_of_pointwise_le_exp {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α))
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ x, ‖(fac x)⁻¹‖ ≤ Real.exp (b x))
    (hsum : ∀ s : Finset α, (∑ x ∈ s, b x) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  by_cases hF : F = 0
  · subst hF
    simpa using exp_nonneg B
  have hnorm :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    hasProd_norm_inv_unconditional hfac hF
  have hprod : ∀ s : Finset α, (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp B := by
    intro s
    have h0 : ∀ x ∈ s, 0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s, b x) := by
      refine Finset.prod_le_exp_sum s (a := fun x => ‖(fac x)⁻¹‖) (b := b) h0 ?_
      intro x hx
      simpa using hterm x
    have h2 : Real.exp (∑ x ∈ s, b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (hsum s)
    exact h1.trans h2
  exact hasProd_le_of_prod_le_exp hnorm hprod
end
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Mathlib_Analysis_Complex_HadamardFactorization_Growth
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Hadamard factorization from a logarithmic growth bound

Assembles the Hadamard quotient, divisor summability, Cartan bounds, and exponential-polynomial
growth into `hadamard_factorization_of_growth`. The pipeline is:

1. `Summability` — Jensen / `logCounting` bounds imply divisor-indexed product convergence
2. `HadamardFactorization` — entire zero-free Hadamard quotient `H = f / (z^k · ∏ E_m)`
3. This file — Cartan circle bounds on `H`, then `zero_free_polynomial_growth_is_exp_poly`
4. `Order` — upgrade to `EntireOfOrderAtMost` and genus `⌊ρ⌋`

All products use `divisorCanonicalProduct` centered at `0` with multiplicities from
`MeromorphicOn.divisor`.

Compared with Tao's proof of the finite-order Hadamard theorem, this file replaces the
good-circle averaging argument by Cartan radius and product bounds.  The purpose is the same:
obtain sufficiently many circles on which the canonical product is not too small, so the zero-free
Hadamard quotient has polynomial exponential growth.  Thus the route is:
Jensen/zero counting (Tao Theorem 2 and Proposition 8) → canonical-product convergence (forward
Exercise 19 input) → Cartan minimum-modulus alternative to the good-circle step → finite-order
Hadamard (Theorem 22).

## Main results

* `hadamard_factorization_of_growth` : entire `f` with log-growth of order `ρ` is a Weierstrass
  product times `exp(P)`
* `zero_free_polynomial_growth_is_exp_poly` (in `ExpPoly`) : the Hadamard quotient is `exp(P)`
* Cartan bounds use `Complex.norm_le_of_mem_ball_of_forall_sphere_norm_le` from `AbsMax`

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [boas1954] and [levin1980] for Weierstrass factors, canonical products, and the classical
  Hadamard product theorem
-/


noncomputable section

open Set Filter _root_.Asymptotics
open scoped Topology BigOperators

namespace Erdos970
namespace Complex.Hadamard
open _root_.Complex

/-- A Cartan radius avoiding the norms of all zeros in a ball gives a zero-free sphere. -/
lemma no_zero_on_sphere_of_norm_image_avoid
    {f : ℂ → ℂ} (hentire : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hr_le_B : r ≤ B)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ B})
    (hr_not_bad :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
      r ∉ small.image a) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  classical
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr_not :
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        ‖divisorZeroIndex₀_val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀_val p‖ := by
    intro p hpB hEq
    have hp_small : p ∈ small := by
      have hp_mem : p ∈ smallSet := by
        simpa [hsmallSet] using hpB
      simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
    have : r ∈ bad := Finset.mem_image.2 ⟨p, hp_small, by simpa [a] using hEq.symm⟩
    exact (hr_not_bad' this).elim
  exact no_zero_on_sphere_of_forall_val_norm_ne (f := f) hentire hnot
    (B := B) (r := r) hrpos hr_le_B hr_not

/-- On a Cartan-admissible circle, the denominator in the Hadamard quotient is not too small. -/
theorem norm_inv_hadamardDenominator_le_exp_on_cartan_circle
    {f : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r →
          ‖(u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr1 : (1 : ℝ) ≤ r := le_trans hRle hR_le_r
  have hpow_inv_le1 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 :=
    Complex.norm_inv_pow_le_one_of_one_le_norm u (analyticOrderNatAt f 0) (by simpa [hur] using hr1)
  let fac : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (u / divisorZeroIndex₀_val p)
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
          weierstrassFactor m (w / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hprod :
      HasProd fac (divisorCanonicalProduct m f (Set.univ : Set ℂ) u) :=
    hloc.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  have : DecidablePred (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => p ∈ small) :=
    Classical.decPred _
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if hp : p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hterm : ∀ p, ‖(fac p)⁻¹‖ ≤ Real.exp (b p) := by
    intro p
    by_cases hp : p ∈ small
    · have hval_ne : r ≠ ap p := by
        intro hEq
        have : r ∈ bad := by
          refine Finset.mem_image.2 ⟨p, hp, ?_⟩
          simp [ap, a, hEq]
        exact (hr_not_bad' this).elim
      have hval0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
      have hmτ : (m : ℝ) ≤ τ := le_trans hmρ (le_of_lt hτ)
      have hnear :
          ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖
            ≤ Real.exp (CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
        simpa [ap] using
          (norm_inv_weierstrassFactor_le_exp_near (m := m) (τ := τ) (r := r)
              (u := u) (a := divisorZeroIndex₀_val p)
              (hur := hur) (ha := hval0) (hr := by simpa [ap] using hval_ne) hmτ)
      simpa [fac, b, hp] using hnear
    · have hlarge : (4 * R : ℝ) < ap p := by
        have : ¬ap p ≤ 4 * R := by
          intro hle
          have : p ∈ small := by
            have hp_mem : p ∈ smallSet := by
              simpa [hsmallSet, ap] using hle
            simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
          exact hp this
        exact lt_of_not_ge this
      have hz' : ‖u / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) :=
        norm_div_le_half_of_norm_le_of_two_mul_lt (z := u) (a := divisorZeroIndex₀_val p)
          (R := 2 * R) (by nlinarith [hRpos]) (by rw [hur]; exact hr_le_2R)
          (by nlinarith [hlarge])
      have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt hτ_lt
      have hfar :
          ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖ ≤
            Real.exp ((2 : ℝ) * (r / ap p) ^ τ) := by
        simpa [ap] using
          (norm_inv_weierstrassFactor_le_exp_far (m := m) (τ := τ) (r := r)
              (u := u) (a := divisorZeroIndex₀_val p)
              (hur := hur) (ha := divisorZeroIndex₀_val_ne_zero p) (hz := hz') hτ_le)
      simpa [fac, b, hp] using hfar
  have hb_le :
      ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
        (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
    intro s
    simpa [small, ap, b, Sτ, Cprod, a, hsmallSet] using
      (Complex.Hadamard.cartan_sum_majorant_le (f := f) (m := m) (τ := τ) (R := R) (r := r)
        (hRpos := hRpos) (hrpos := lt_of_lt_of_le hRpos hR_le_r)
        (hR_le_r := hR_le_r) (hτ_nonneg := hτ_nonneg)
        (smallSet := smallSet) (hsmall_fin := hsmall_fin) (hsmallSet := hsmallSet)
        (hsumτ := hsumτ)
        (hr_phi := by
          simpa [small, a, one_mul] using hr_phi)
        s)
  have hcprod_inv :
      ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
        Real.exp (Cprod * (1 + r) ^ τ) := by
    refine hasProd_norm_inv_le_exp_of_pointwise_le_exp
      (α := divisorZeroIndex₀ f (Set.univ : Set ℂ)) (fac := fac)
      (F := divisorCanonicalProduct m f (Set.univ : Set ℂ) u)
      hprod (b := b) (B := Cprod * (1 + r) ^ τ) ?_ ?_
    · exact hterm
    · intro s
      exact hb_le s
  have hmul :
      ‖(u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        =
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
        ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    simp [mul_inv_rev, mul_comm]
  rw [hmul]
  have :
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
          ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ 1 * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hpow_inv_le1 hcprod_inv (by positivity) (by positivity)
  simpa using this

/-- On a Cartan-admissible circle, the Hadamard quotient is exponentially bounded. -/
theorem hadamardQuotient_norm_le_exp_on_cartan_circle_jb247_oai
    {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
    (hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀_val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R hrpos smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hden_eq :
      f u =
        H u * (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
  have hfu_ne : f u ≠ 0 := by
    have hr_le_4R : r ≤ 4 * R := by nlinarith [hr_le_2R, hRpos]
    exact no_zero_on_sphere_of_norm_image_avoid (f := f) hentire hnot
      (B := 4 * R) (r := r) hrpos hr_le_4R smallSet hsmall_fin hsmallSet
      (by simpa [small, a] using hr_not_bad) u hur
  have hden_ne :
      (u ^ analyticOrderNatAt f 0 *
        divisorCanonicalProduct m f (Set.univ : Set ℂ) u) ≠ 0 := by
    intro hden0
    have : f u = 0 := by simpa [hden0] using hden_eq
    exact hfu_ne this
  have hHu :
      H u =
        f u / (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
    exact eq_div_of_mul_eq hden_ne (Eq.symm hden_eq)
  have hf_u : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
    simpa [hur] using hf_boundτ u
  have hden_inv :
      ‖(u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (norm_inv_hadamardDenominator_le_exp_on_cartan_circle
        (f := f) (ρ := ρ) (τ := τ) (m := m)
        hmρ hτ hτ_lt hτ_nonneg h_sum hsumτ
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R
        smallSet hsmall_fin hsmallSet
        (by simpa [small, a] using hr_not_bad)
        (by simpa [small, a, one_mul] using hr_phi)
        u hur)
  have :
      ‖H u‖ ≤
        ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    have :
        ‖H u‖ =
          ‖f u /
            (u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)‖ := by
      simp [hHu]
    simp [div_eq_mul_inv, norm_inv, this]
  have hmul :
      ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hf_u hden_inv (by positivity) (by positivity)
  have hexp :
      Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ)
        = Real.exp ((Cf + Cprod) * (1 + r) ^ τ) := by
    simp [Real.exp_add, add_mul, add_comm]
  have : ‖H u‖ ≤ Real.exp ((Cf + Cprod) * (1 + r) ^ τ) :=
    (this.trans hmul).trans_eq hexp
  have hslack :
      Real.exp ((Cf + Cprod) * (1 + r) ^ τ) ≤
        Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (1 + r) ^ τ := by positivity
    nlinarith
  exact this.trans hslack

end Complex.Hadamard
end Erdos970
end
end

theorem solution : type_of% @Erdos970.Complex.Hadamard.hadamardQuotient_norm_le_exp_on_cartan_circle_jb247_oai := @Erdos970.Complex.Hadamard.hadamardQuotient_norm_le_exp_on_cartan_circle_jb247_oai
