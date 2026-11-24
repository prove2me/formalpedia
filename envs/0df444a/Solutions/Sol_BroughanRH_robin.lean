-- Prove2me | solution 1 for BroughanRH.robin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T03:26:23.71314+00:00
-- url     : https://prove2.me/submissions/9aee22cb-68e0-4166-a083-a0a989f4edef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RobinRHParts_robin_direct_5041_11041
import Theorems.Thm_RobinRHParts_robin_direct_11041_17041
import Theorems.Thm_RobinRHParts_robin_direct_17041_22027
import Theorems.Thm_RobinRHParts_robin_logrange_10_487
import Theorems.Thm_RobinRHParts_robin_logrange_487_1009
import Theorems.Thm_RobinRHParts_robin_RH_logrange_1000_1100000
import Theorems.Thm_RobinRHParts_robin_RH_log_ge_1100000
import Theorems.Thm_riemann_hypothesis

theorem solution :
    ∀ n : ℕ, 5040 < n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have hRH : RiemannHypothesis := riemann_hypothesis
  intro n hn
  by_cases hs : n < 22027
  · by_cases h1 : n < 11041
    · exact RobinRHParts.robin_direct_5041_11041 n (by omega) h1
    by_cases h2 : n < 17041
    · exact RobinRHParts.robin_direct_11041_17041 n (by omega) h2
    · exact RobinRHParts.robin_direct_17041_22027 n (by omega) hs
  have hlog : (10:ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 ^ 10 ≤ (2.7182818286:ℝ)^10 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 10
    have h3 : (22027:ℝ) ≤ n := by exact_mod_cast (not_lt.mp hs)
    rw [h1]; norm_num at h2 ⊢; linarith
  by_cases h487 : Real.log n < 487
  · exact RobinRHParts.robin_logrange_10_487 n hlog h487
  by_cases h1009 : Real.log n < 1009
  · exact RobinRHParts.robin_logrange_487_1009 n (not_lt.mp h487) h1009
  by_cases hmid : Real.log n < 1100000
  · exact RobinRHParts.robin_RH_logrange_1000_1100000 hRH n (by linarith [not_lt.mp h1009]) hmid
  · exact RobinRHParts.robin_RH_log_ge_1100000 hRH n (not_lt.mp hmid)
