-- Prove2me | solution 2 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:22.271823+00:00
-- url     : https://prove2.me/submissions/2c57aa27-d14f-483d-a147-cfeecbd1cb72

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_geom
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_split
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_fiber_le

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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) (a0 : ℕ) :
    primeTermWeight x N p ≤ Real.log p * ((a0 : ℝ) + 2 * x / (p : ℝ) ^ (a0 + 1)) := by
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hcn : ∀ a ∈ Icc 1 N, cn x (p ^ a) = Real.log p * min 1 (x / (p : ℝ) ^ a) := by
    intro a ha
    rw [mem_Icc] at ha
    unfold cn
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    push_cast
    rfl
  calc primeTermWeight x N p ≤ ∑ a ∈ Icc 1 N, cn x (p ^ a) :=
        gl2a5_fiber_le N p (cn x) (gl2a5_cn_nonneg hx)
    _ = ∑ a ∈ Icc 1 N, Real.log p * min 1 (x / (p : ℝ) ^ a) := Finset.sum_congr rfl hcn
    _ ≤ ∑ a ∈ Icc 1 a0, Real.log p * min 1 (x / (p : ℝ) ^ a)
        + ∑ a ∈ Ioc a0 N, Real.log p * min 1 (x / (p : ℝ) ^ a) :=
        gl2a5_split _ (fun a => mul_nonneg hlog (le_min zero_le_one (by positivity))) a0 N
    _ ≤ ∑ a ∈ Icc 1 a0, Real.log p + ∑ a ∈ Ioc a0 N, Real.log p * x * ((p : ℝ)⁻¹) ^ a := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro a _
          exact mul_le_of_le_one_right hlog (min_le_left _ _)
        · apply Finset.sum_le_sum; intro a _
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hlog
          refine (min_le_right _ _).trans (le_of_eq ?_)
          rw [inv_pow, div_eq_mul_inv]
    _ ≤ (a0 : ℝ) * Real.log p + Real.log p * x * (2 * ((p : ℝ)⁻¹) ^ (a0 + 1)) := by
        apply add_le_add
        · rw [Finset.sum_const, Nat.card_Icc]; simp
        · rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply gl2a5_geom _ (by positivity)
          rw [inv_le_comm₀ hp0 (by norm_num)]
          norm_num
          exact hp.two_le
    _ = _ := by
        rw [inv_pow]; field_simp
end Formalism.HermitianLattices.GL2PrimeSums
