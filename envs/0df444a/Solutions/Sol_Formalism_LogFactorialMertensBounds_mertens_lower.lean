-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.mertens_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:34.868343+00:00
-- url     : https://prove2.me/submissions/4da12490-40e6-47bc-a4c9-ba7913a438ec

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_sum_log_eq_log_factorial
import Theorems.Thm_Formalism_LogFactorialMertensBounds_sum_log_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) : Real.log k - 1 ≤ A k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hfl : Real.log (k.factorial : ℝ) ≤ k * A k := by
    rw [← sum_log_eq_log_factorial, sum_log_eq, A, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hd : ((k / n : ℕ) : ℝ) ≤ (k:ℝ) / n := Nat.cast_div_le
    have h3 : (k:ℝ) * (Λ n / n) = Λ n * ((k:ℝ) / n) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left hd hΛ
  have hst : k * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (k:ℝ) hk0.le k
    have hpos : (0:ℝ) < (k:ℝ) ^ k / k.factorial := by positivity
    have h2 := Real.log_le_log hpos h
    rw [Real.log_exp, Real.log_div (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)),
      Real.log_pow] at h2
    linarith
  have h5 : (k:ℝ) * (Real.log k - 1) ≤ k * A k := by nlinarith
  exact le_of_mul_le_mul_left h5 hk0
end Formalism.LogFactorialMertensBounds
