-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.mertens_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:47.087491+00:00
-- url     : https://prove2.me/submissions/c40034ee-0d6b-40d9-baa7-a13ad5c189bb

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
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) : A k ≤ Real.log k + (Real.log 4 + 4) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hpsi : ∑ n ∈ Finset.Ioc 0 k, Λ n ≤ (Real.log 4 + 4) * k := by
    have h := Chebyshev.psi_le_const_mul_self (x := (k:ℝ)) hk0.le
    simpa [Chebyshev.psi] using h
  have hfact : Real.log (k.factorial : ℝ) ≤ k * Real.log k := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow k)
  have hmain : (k:ℝ) * A k ≤ ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) +
      ∑ n ∈ Finset.Ioc 0 k, Λ n := by
    rw [A, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnpos : 0 < n := hn.1
    have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
    have h1N : k < (k / n + 1) * n := by
      rw [Nat.add_mul, one_mul]
      exact Nat.lt_div_mul_add hnpos
    have h1R : (k:ℝ) ≤ (((k / n : ℕ) : ℝ) + 1) * n := by exact_mod_cast h1N.le
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (k:ℝ) / n ≤ ((k / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hnR]
      exact h1R
    have h3 : (k:ℝ) * (Λ n / n) = Λ n * ((k:ℝ) / n) := by ring
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left h2 hΛ]
  rw [← sum_log_eq, sum_log_eq_log_factorial] at hmain
  have h4 : (k:ℝ) * A k ≤ k * (Real.log k + (Real.log 4 + 4)) := by nlinarith
  exact le_of_mul_le_mul_left h4 hk0
end Formalism.LogFactorialMertensBounds
