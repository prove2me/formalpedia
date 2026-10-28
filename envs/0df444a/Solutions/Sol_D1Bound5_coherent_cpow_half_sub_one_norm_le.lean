-- Prove2me | solution 1 for D1Bound5.coherent_cpow_half_sub_one_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:23.9498+00:00
-- url     : https://prove2.me/submissions/5be08ec0-bc11-4b89-9f46-f3bcb68fcc64

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_le_half
import Theorems.Thm_D1Bound5_halfBinomialCoeff_hasSum_cpow

section
open Finset

namespace D1Bound5

/-- A geometric bound for the actual principal half-power remainder.
This follows from its convergent binomial series and the coefficient
bound `|b_n| <= 1/2`, without selecting a new square-root sign. -/
theorem _root_.solution
    (w : ℂ) (hw : ‖w‖ < 1) :
    ‖((1 + w) ^ (1 / 2 : ℂ)) - 1‖ ≤
      (1 / 2 : ℝ) * ‖w‖ / (1 - ‖w‖) := by
  have hb0 : (halfBinomialCoeff 0 : ℂ) = 1 := by simp [halfBinomialCoeff]
  have htail : HasSum
      (fun n : ℕ => (halfBinomialCoeff (n + 1) : ℂ) * w ^ (n + 1))
      (((1 + w) ^ (1 / 2 : ℂ)) - 1) := by
    simpa only [Finset.sum_range_one, pow_zero, mul_one, hb0] using
      (hasSum_nat_add_iff' 1).2 (halfBinomialCoeff_hasSum_cpow w hw)
  have hr : ‖(‖w‖ : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)] using hw
  have hmajor : HasSum (fun n : ℕ => (1 / 2 : ℝ) * ‖w‖ ^ (n + 1))
      ((1 / 2 : ℝ) * ‖w‖ / (1 - ‖w‖)) := by
    have h := (hasSum_geometric_of_norm_lt_one hr).mul_left ((1 / 2 : ℝ) * ‖w‖)
    refine h.congr_fun ?_
    intro n
    rw [pow_succ]
    ring
  have hterm (n : ℕ) :
      ‖(halfBinomialCoeff (n + 1) : ℂ) * w ^ (n + 1)‖ ≤
        (1 / 2 : ℝ) * ‖w‖ ^ (n + 1) := by
    calc
      ‖(halfBinomialCoeff (n + 1) : ℂ) * w ^ (n + 1)‖ =
        |halfBinomialCoeff (n + 1)| * ‖w‖ ^ (n + 1) := by
          simp [Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (halfBinomialCoeff_abs_le_half (n + 1) (by omega)) (by positivity)
  calc
    ‖((1 + w) ^ (1 / 2 : ℂ)) - 1‖ =
      ‖∑' n : ℕ, (halfBinomialCoeff (n + 1) : ℂ) * w ^ (n + 1)‖ := by
        rw [htail.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(halfBinomialCoeff (n + 1) : ℂ) * w ^ (n + 1)‖ :=
      norm_tsum_le_tsum_norm htail.summable.norm
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) * ‖w‖ ^ (n + 1) :=
      htail.summable.norm.tsum_le_tsum hterm hmajor.summable
    _ = _ := hmajor.tsum_eq



end D1Bound5
end
