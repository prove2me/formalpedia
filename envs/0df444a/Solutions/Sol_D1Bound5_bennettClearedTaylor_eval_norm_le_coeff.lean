-- Prove2me | solution 1 for D1Bound5.bennettClearedTaylor_eval_norm_le_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:30.701369+00:00
-- url     : https://prove2.me/submissions/700614f3-1b23-4310-a692-baccbd24269c

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettCoefficientMajorant_Definitions
import Theorems.Thm_D1Bound5_bennettSeries_coeff_C_add_X_pow
import Theorems.Thm_D1Bound5_bennett_shifted_half_choose_abs_le

section
open Finset

namespace D1Bound5









theorem bennettNumeratorMajorant_coeff (U : ℝ) (hU : U ≠ 0)
    (k h : ℕ) (hh : h ≤ k) :
    PowerSeries.coeff h (bennettNumeratorMajorant U k) =
      (Nat.choose (k + 1) h : ℝ) * U ^ (k - h) := by
  rw [bennettNumeratorMajorant, PowerSeries.coeff_C_mul,
    bennettSeries_coeff_C_add_X_pow]
  have hexp : k + 1 - h = k - h + 1 := by omega
  rw [hexp, pow_succ]
  field_simp [hU]
  <;> ring





/-- The actual complex local residue Taylor expression is bounded by the
coefficient of the explicit positive numerator/pole majorant. -/
theorem _root_.solution
    (k t : ℕ) (ht : t ≤ k) (a N : ℂ)
    (B : PowerSeries ℂ) (D : PowerSeries ℝ)
    (hU : 0 < ‖N + a‖)
    (hB : ∀ h, ‖PowerSeries.coeff h B‖ ≤ PowerSeries.coeff h D) :
    ‖(bennettClearedTaylor k t (1 / 2 : ℂ) a B).eval N‖ ≤
      PowerSeries.coeff t (bennettNumeratorMajorant ‖N + a‖ k * D) := by
  unfold bennettClearedTaylor
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  rw [PowerSeries.coeff_mul]
  calc
    _ ≤ ∑ hu ∈ antidiagonal t,
      ‖(Ring.choose ((k : ℂ) + 1 / 2) hu.1 * PowerSeries.coeff hu.2 B) *
        (N + a) ^ (k - hu.1)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro hu hhu
      have hh : hu.1 ≤ k := by
        have hsum := Finset.mem_antidiagonal.mp hhu
        omega
      have hchoose : ‖Ring.choose ((k : ℂ) + 1 / 2) hu.1‖ ≤
          (Nat.choose (k + 1) hu.1 : ℝ) := by
        have hcast : Ring.choose ((k : ℂ) + 1 / 2) hu.1 =
            Complex.ofReal (Ring.choose ((k : ℝ) + 1 / 2) hu.1) := by
          simpa using
            (Ring.map_choose (algebraMap ℝ ℂ) ((k : ℝ) + 1 / 2) hu.1).symm
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        exact bennett_shifted_half_choose_abs_le k hu.1 hh
      rw [norm_mul, norm_mul, norm_pow,
        bennettNumeratorMajorant_coeff _ hU.ne' k hu.1 hh]
      calc
        _ ≤ ((Nat.choose (k + 1) hu.1 : ℝ) * PowerSeries.coeff hu.2 D) *
            ‖N + a‖ ^ (k - hu.1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hchoose (hB hu.2) (norm_nonneg _) (Nat.cast_nonneg _))
            (pow_nonneg (norm_nonneg _) _)
        _ = _ := by ring

end D1Bound5
end
