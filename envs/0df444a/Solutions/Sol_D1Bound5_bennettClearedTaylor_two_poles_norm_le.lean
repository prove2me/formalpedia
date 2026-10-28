-- Prove2me | solution 1 for D1Bound5.bennettClearedTaylor_two_poles_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:44.860736+00:00
-- url     : https://prove2.me/submissions/302c0eda-bfc1-456c-880d-95695bde90aa

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
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_weighted_norm_le
import Theorems.Thm_D1Bound5_bennett_two_row_radius_power_le

section
namespace D1Bound5



/-- The extra row pole cancels the coefficient radius, yielding a uniform
bound for every actual row. The condition 2r≤both distances holds at r=2u/5. -/
theorem _root_.solution
    (a N d e : ℂ) (k d0 d1 d2 : ℕ) (hk : 1 ≤ k)
    (hrow : d0 + d1 + d2 = 1)
    (r : ℝ) (hr : 0 < r) (hU : 0 < ‖N + a‖)
    (hd : 2 * r ≤ ‖d‖) (he : 2 * r ≤ ‖e‖) :
    ‖(bennettClearedTaylor k (k + d0 - 1) (1 / 2 : ℂ) a
      (bennettPoleSeries d (k + d1) * bennettPoleSeries e (k + d2))).eval N‖ ≤
      ((‖N + a‖ + r) / ‖N + a‖) *
        ((‖N + a‖ + r) / (r * (‖d‖ - r) * (‖e‖ - r))) ^ k := by
  have hDr : r ≤ ‖d‖ - r := by linarith
  have hEr : r ≤ ‖e‖ - r := by linarith
  have hD : 0 < ‖d‖ - r := hr.trans_le hDr
  have hE : 0 < ‖e‖ - r := hr.trans_le hEr
  have hbase : 0 < r * (‖d‖ - r) * (‖e‖ - r) := mul_pos (mul_pos hr hD) hE
  have ht : k + d0 - 1 ≤ k := by omega
  have hw := bennettClearedTaylor_two_poles_weighted_norm_le a N d e
    k (k + d0 - 1) (k + d1) (k + d2) ht r hr.le hU (by linarith) (by linarith)
  let Z := ‖(bennettClearedTaylor k (k + d0 - 1) (1 / 2 : ℂ) a
    (bennettPoleSeries d (k + d1) * bennettPoleSeries e (k + d2))).eval N‖
  have hden : Z * (r ^ (k + d0 - 1) * (‖d‖ - r) ^ (k + d1) *
      (‖e‖ - r) ^ (k + d2)) ≤ (‖N + a‖ + r) ^ (k + 1) / ‖N + a‖ := by
    calc
      _ = (Z * r ^ (k + d0 - 1)) *
          ((‖d‖ - r) ^ (k + d1) * (‖e‖ - r) ^ (k + d2)) := by ring
      _ ≤ (((‖N + a‖ + r) ^ (k + 1) / ‖N + a‖) *
          ((‖d‖ - r)⁻¹ ^ (k + d1) * (‖e‖ - r)⁻¹ ^ (k + d2))) *
            ((‖d‖ - r) ^ (k + d1) * (‖e‖ - r) ^ (k + d2)) :=
        mul_le_mul_of_nonneg_right hw (mul_nonneg (pow_nonneg hD.le _) (pow_nonneg hE.le _))
      _ = _ := by
        have hcancel (x : ℝ) (hx : x ≠ 0) (m : ℕ) : (x⁻¹)^m * x^m = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
        calc
          _ = ((‖N + a‖ + r) ^ (k + 1) / ‖N + a‖) *
              (((‖d‖ - r)⁻¹ ^ (k + d1) * (‖d‖ - r) ^ (k + d1)) *
                ((‖e‖ - r)⁻¹ ^ (k + d2) * (‖e‖ - r) ^ (k + d2))) := by ring
          _ = _ := by
            rw [hcancel _ hD.ne' (k + d1), hcancel _ hE.ne' (k + d2), one_mul, mul_one]
  have hpow := bennett_two_row_radius_power_le r (‖d‖ - r) (‖e‖ - r)
    hr hDr hEr k d0 d1 d2 hk hrow
  have hsimple : Z ≤ ((‖N + a‖ + r) ^ (k + 1) / ‖N + a‖) /
      (r * (‖d‖ - r) * (‖e‖ - r)) ^ k := by
    apply (le_div_iff₀ (pow_pos hbase _)).mpr
    exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans hden
  calc
    _ = Z := rfl
    _ ≤ _ := hsimple
    _ = _ := by rw [div_pow, pow_succ]; ring

end D1Bound5
end
