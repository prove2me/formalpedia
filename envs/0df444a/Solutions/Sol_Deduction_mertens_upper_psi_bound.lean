-- Prove2me | solution 1 for Deduction.mertens_upper_psi_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:03.873788+00:00
-- url     : https://prove2.me/submissions/e055c189-ba68-43ed-b2ae-528d72e4a69c

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mertensUpper
import Theorems.Thm_Deduction_mertens_upper_sum_log
import Theorems.Thm_Deduction_mertens_upper_log_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n + 1 + Real.log N ≤ 3 * N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  by_cases h25 : 25 ≤ N
  · have hp := Chebyshev.psi_le hN'
    rw [Chebyshev.psi, Nat.floor_natCast] at hp
    have h25' : (25 : ℝ) ≤ N := by exact_mod_cast h25
    have hs : 5 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by linarith)
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    have hL : Real.log N = 2 * Real.log (Real.sqrt N) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have hl := mertens_upper_log_le (Real.sqrt N) 4 (by linarith) (by norm_num)
    set s := Real.sqrt N
    have hl' : Real.log N ≤ 0.78 + s / 2 := by linarith
    have h5 : 2 * s * Real.log N ≤ 2 * s * (0.78 + s / 2) :=
      mul_le_mul_of_nonneg_left hl' (by linarith)
    have h6 : Real.log 4 * N ≤ 1.39 * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · have h1 : ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log n :=
      Finset.sum_le_sum fun n _ => ArithmeticFunction.vonMangoldt_le_log
    have h2 := mertens_upper_sum_log N hN
    have h24 : (N : ℝ) ≤ 24 := by exact_mod_cast (by omega : N ≤ 24)
    by_cases h3 : 3 ≤ N
    · have h3' : (3 : ℝ) ≤ N := by exact_mod_cast h3
      have hl := mertens_upper_log_le N 16 (by linarith) (by norm_num)
      have hl' : Real.log N ≤ 1.78 + N / 16 := by linarith
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (1.78 + N / 16) :=
        mul_le_mul_of_nonneg_left hl' (by linarith)
      nlinarith
    · have h2' : (N : ℝ) ≤ 2 := by exact_mod_cast (by omega : N ≤ 2)
      have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (N - 1) :=
        mul_le_mul_of_nonneg_left hl (by linarith)
      nlinarith
end Deduction
