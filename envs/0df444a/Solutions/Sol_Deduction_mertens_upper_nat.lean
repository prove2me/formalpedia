-- Prove2me | solution 1 for Deduction.mertens_upper_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:01.930593+00:00
-- url     : https://prove2.me/submissions/d6048b23-72af-44ee-b969-7d5b78c990e6

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mertensUpper
import Theorems.Thm_Deduction_mertens_upper_sum_log
import Theorems.Thm_Deduction_mertens_upper_psi_bound

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
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log N + 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hid := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at hid
  simp only [ArithmeticFunction.log_apply] at hid
  have h1 := mertens_upper_sum_log N hN
  have h2 := mertens_upper_psi_bound N hN
  have h3 : N * ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) +
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have : N ≤ (N / n + 1) * n := by
        have := Nat.lt_div_mul_add (a := N) hn0
        nlinarith
      exact_mod_cast this
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    calc (N : ℝ) * (ArithmeticFunction.vonMangoldt n / n)
        = ArithmeticFunction.vonMangoldt n * ((N : ℝ) / n) := by ring
      _ ≤ ArithmeticFunction.vonMangoldt n * (((N / n : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hlt hΛ
      _ = _ := by ring
  rw [← hid] at h3
  refine le_of_mul_le_mul_left ?_ hN'
  nlinarith
end Deduction
