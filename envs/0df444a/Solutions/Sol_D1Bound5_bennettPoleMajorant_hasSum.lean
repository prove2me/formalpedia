-- Prove2me | solution 1 for D1Bound5.bennettPoleMajorant_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:31.577927+00:00
-- url     : https://prove2.me/submissions/b3c99d83-5102-4eef-8dae-85a185c2ae7c

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
import Definitions.Def_D1Bound5_BennettPositiveSeries_Definitions
import Theorems.Thm_D1Bound5_bennettPoleMajorant_coeff
import Theorems.Thm_D1Bound5_bennett_negative_binomial_abs_hasSum

section
open Finset

namespace D1Bound5









/-- The actual weighted sum of the positive pole majorant, including pole
order zero. The radius is strictly smaller than the positive displacement. -/
theorem _root_.solution
    (d r : ℝ) (p : ℕ) (hd : 0 < d) (hr0 : 0 ≤ r) (hrd : r < d) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (bennettPoleMajorant d p) * r ^ n)
      ((d-r)⁻¹ ^ p) := by
  cases p with
  | zero =>
      convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) using 1
      · ext n
        by_cases hn : n = 0
        · subst n
          simp
        · simp [bennettPoleMajorant_coeff, Ring.choose_zero_ite, hn]
      · simp
  | succ p =>
      have hratio0 : 0 ≤ r/d := div_nonneg hr0 hd.le
      have hratio1 : r/d < 1 := (div_lt_one hd).2 hrd
      have hp : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
      have hs := bennett_negative_binomial_abs_hasSum
        ((p + 1 : ℕ) : ℝ) (r/d) hp hratio0 hratio1
      have hscaled := hs.mul_left (d⁻¹ ^ (p+1))
      have hbase : 0 < 1-r/d := sub_pos.mpr hratio1
      have hsub : 0 < d-r := sub_pos.mpr hrd
      have hinner : d⁻¹*(1-r/d)⁻¹ = (d-r)⁻¹ := by
        field_simp [hd.ne', hbase.ne', hsub.ne'] <;> ring
      have htotal : d⁻¹ ^ (p+1) * (1/(1-r/d)^((p+1 : ℕ) : ℝ)) =
          (d-r)⁻¹ ^ (p+1) := by
        rw [Real.rpow_natCast]
        calc
          _ = (d⁻¹ * (1-r/d)⁻¹) ^ (p+1) := by
            simp only [mul_pow, inv_pow, one_div]
          _ = _ := by rw [hinner]
      rw [htotal] at hscaled
      have hfun :
          (fun n : ℕ => PowerSeries.coeff n (bennettPoleMajorant d (p+1)) * r^n) =
          (fun n : ℕ => d⁻¹ ^ (p+1) *
            (|Ring.choose (-((p+1 : ℕ) : ℝ)) n| * (r/d)^n)) := by
        funext n
        simp only [bennettPoleMajorant_coeff, pow_add, div_eq_mul_inv, mul_pow]
        ring
      rw [hfun]
      exact hscaled











end D1Bound5
end
