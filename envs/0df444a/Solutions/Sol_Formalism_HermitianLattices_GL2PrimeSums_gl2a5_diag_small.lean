-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:53.658186+00:00
-- url     : https://prove2.me/submissions/7a9c1b16-d33d-42c6-8c11-7f53f3548aa0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_not_prime
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_small
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_log
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_count
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_log_le_sqrt

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
    (hx : Real.exp 1 ≤ x) (N : ℕ) :
    ∑ p ∈ Icc 1 ⌊x⌋₊, (primeTermWeight x N p) ^ 2 ≤ 30 * x * Real.log x := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpt : ∀ p ∈ Icc 1 ⌊x⌋₊, (primeTermWeight x N p) ^ 2 ≤
      3 * Real.log x * (4 * Λ p + Real.log x * (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) := by
    intro p _
    have h0 := gl2a5s_nonneg (by linarith : (0 : ℝ) ≤ x) N p
    have h3 := gl2a5s_le_log hx N p
    have h4 : primeTermWeight x N p ≤
        4 * Λ p + Real.log x * (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) := by
      by_cases hp : p.Prime
      · have h5 := gl2a5s_le_small hx1 N hp
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        rw [vonMangoldt_apply_prime hp]
        split_ifs with hs
        · linarith
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
          have h6 : x < (p : ℝ) ^ 2 := (Real.sqrt_lt' hp0).1 (not_le.1 hs)
          have h7 : Real.log x ≤ Real.log ((p : ℝ) ^ 2) := Real.log_le_log (by linarith) h6.le
          rw [Real.log_pow] at h7
          push_cast at h7
          linarith
      · rw [gl2a5s_not_prime x N hp]
        have : 0 ≤ Λ p := vonMangoldt_nonneg
        split_ifs <;> positivity
    rw [sq]
    exact mul_le_mul h3 h4 h0 (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := hψ ⌊x⌋₊
  have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h3 := gl2a5_count ⌊x⌋₊ (Real.sqrt x) (Real.sqrt_nonneg x)
  have h4 := gl2a5_log_le_sqrt hx1
  have h5 : Real.log x * (∑ p ∈ Icc 1 ⌊x⌋₊, (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) ≤
      2 * Real.sqrt x * Real.sqrt x :=
    mul_le_mul h4 h3 (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (by positivity)
  rw [mul_assoc, Real.mul_self_sqrt (by linarith)] at h5
  have h6 : 4 * ∑ i ∈ Icc 1 ⌊x⌋₊, Λ i + Real.log x *
      (∑ p ∈ Icc 1 ⌊x⌋₊, (if (p : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0)) ≤ 10 * x := by linarith
  calc _ ≤ 3 * Real.log x * (10 * x) := mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by ring
end Formalism.HermitianLattices.GL2PrimeSums
