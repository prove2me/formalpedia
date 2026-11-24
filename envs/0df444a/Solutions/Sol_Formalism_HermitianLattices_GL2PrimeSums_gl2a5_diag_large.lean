-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.532743+00:00
-- url     : https://prove2.me/submissions/9e5c90ef-1186-4240-8a76-d1e335a30e4e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_abel
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_log_sq_tail
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_not_prime
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_large
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_g_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : 3 ≤ x) (N : ℕ) :
    ∑ p ∈ Ioc ⌊x⌋₊ N, (primeTermWeight x N p) ^ 2 ≤ 32 * x * Real.log x := by
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact he
  have hK : 3 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  set K := ⌊x⌋₊ with hKdef
  have hpt : ∀ p ∈ Ioc K N, (primeTermWeight x N p) ^ 2 ≤
      4 * x ^ 2 * (Λ p * (Real.log p / (p : ℝ) ^ 2)) := by
    intro p _
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hp : p.Prime
    · have h0 := gl2a5s_nonneg hx0.le N p
      have h1 := gl2a5s_le_large hx0.le N hp
      rw [vonMangoldt_apply_prime hp]
      calc (primeTermWeight x N p) ^ 2 ≤ (2 * x * (Real.log p / p)) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = _ := by ring
    · rw [gl2a5s_not_prime x N hp]
      have : 0 ≤ Λ p := vonMangoldt_nonneg
      have h : 0 ≤ 4 * x ^ 2 * (Λ p * (Real.log p / (p : ℝ) ^ 2)) := by positivity
      simpa using h
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  have h1 := gl2a5_abel hψ (fun n => Real.log n / (n : ℝ) ^ 2) K
    (fun n hn => gl2a5_g_anti (by omega))
    (fun n _ => by
      have := Real.log_natCast_nonneg n
      positivity) N
  have h2 := gl2a5_log_sq_tail (K + 1) (by omega) N
  have hy : x < ((K + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one x
  set y : ℝ := ((K + 1 : ℕ) : ℝ) with hydef
  have hy0 : 0 < y := by linarith
  have h3 : Real.log y / y ≤ Real.log x / x :=
    Real.log_div_self_antitoneOn (by simpa using he) (by simpa using he.trans hy.le) hy.le
  have h4 : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hy.le
  have e1 : 2 * ((K : ℝ) + 1) * (Real.log y / y ^ 2) = 2 * (Real.log y / y) := by
    have : (K : ℝ) + 1 = y := by rw [hydef]; push_cast; rfl
    rw [this]; field_simp
  have e2 : (Real.log y + 2) / y = Real.log y / y + 2 * (1 / y) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h5 : ∑ n ∈ Ioc K N, Λ n * (Real.log n / (n : ℝ) ^ 2) ≤ 4 * (Real.log x / x) + 4 * (1 / x) := by
    linarith
  calc _ ≤ 4 * x ^ 2 * (4 * (Real.log x / x) + 4 * (1 / x)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 16 * x * Real.log x + 16 * x := by field_simp; ring
    _ ≤ _ := by nlinarith
end Formalism.HermitianLattices.GL2PrimeSums
