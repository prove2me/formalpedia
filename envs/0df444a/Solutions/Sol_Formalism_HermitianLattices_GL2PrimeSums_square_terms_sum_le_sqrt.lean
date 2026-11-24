-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.square_terms_sum_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.502266+00:00
-- url     : https://prove2.me/submissions/69fc0b21-24c3-476d-b03d-eff743e0d456

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_abel
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_split
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_inv_sq_tail
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg

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
theorem _root_.solution (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => IsSquare n), cn x n ≤ 6 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  have hK : 1 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by simpa using hs1)
  set K := ⌊Real.sqrt x⌋₊ with hKdef
  have hcn : ∀ m ∈ Icc 1 N, cn x (m ^ 2) = Λ m * min 1 (x / (m : ℝ) ^ 2) := by
    intro m _
    unfold cn
    rw [vonMangoldt_apply_pow (by norm_num)]
    push_cast
    rfl
  have hΛ : ∀ m : ℕ, 0 ≤ Λ m := fun m => vonMangoldt_nonneg
  have hy : Real.sqrt x < ((K + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  calc ∑ n ∈ (primesLeFinset N).filter (fun n => IsSquare n), cn x n
      ≤ ∑ n ∈ (Icc 1 N).image (fun m => m ^ 2), cn x n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [primesLeFinset, mem_filter, mem_Icc] at hn
          obtain ⟨⟨⟨h1, hN⟩, _⟩, m, rfl⟩ := hn
          rw [mem_image]
          refine ⟨m, ?_, by ring⟩
          rw [mem_Icc]
          have hm : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · subst h0; simp at h1
            · exact h0
          exact ⟨hm, (Nat.le_mul_self m).trans hN⟩
        · intro n _ _; exact gl2a5_cn_nonneg hx0.le n
    _ = ∑ m ∈ Icc 1 N, cn x (m ^ 2) := by
        apply Finset.sum_image
        intro a _ b _ hab
        exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hab
    _ = ∑ m ∈ Icc 1 N, Λ m * min 1 (x / (m : ℝ) ^ 2) := Finset.sum_congr rfl hcn
    _ ≤ ∑ m ∈ Icc 1 K, Λ m * min 1 (x / (m : ℝ) ^ 2)
        + ∑ m ∈ Ioc K N, Λ m * min 1 (x / (m : ℝ) ^ 2) :=
        gl2a5_split _ (fun m => mul_nonneg (hΛ m) (le_min zero_le_one (by positivity))) K N
    _ ≤ ∑ m ∈ Icc 1 K, Λ m + x * ∑ m ∈ Ioc K N, Λ m * (1 / (m : ℝ) ^ 2) := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro m _
          exact mul_le_of_le_one_right (hΛ m) (min_le_left _ _)
        · rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro m _
          calc Λ m * min 1 (x / (m : ℝ) ^ 2) ≤ Λ m * (x / (m : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) (hΛ m)
            _ = _ := by ring
    _ ≤ 2 * Real.sqrt x + x * (4 / Real.sqrt x) := by
        apply add_le_add
        · exact (hψ K).trans (by linarith [Nat.floor_le (Real.sqrt_nonneg x)])
        · apply mul_le_mul_of_nonneg_left _ hx0.le
          have h1 := gl2a5_abel hψ (fun n => 1 / (n : ℝ) ^ 2) K
            (fun n hn => by
              have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
              apply one_div_le_one_div_of_le (by positivity)
              push_cast
              nlinarith)
            (fun n _ => by positivity) N
          have h2 := gl2a5_inv_sq_tail (K + 1) (by omega) N
          set y : ℝ := ((K + 1 : ℕ) : ℝ) with hydef
          have hy0 : 0 < y := by linarith
          have e1 : 2 * ((K : ℝ) + 1) * (1 / y ^ 2) = 2 * (1 / y) := by
            have : (K : ℝ) + 1 = y := by rw [hydef]; push_cast; rfl
            rw [this]; field_simp
          rw [e1] at h1
          have h4 : 1 / y ≤ 1 / Real.sqrt x := one_div_le_one_div_of_le (by linarith) hy.le
          have e2 : 4 / Real.sqrt x = 4 * (1 / Real.sqrt x) := by ring
          rw [e2]
          linarith
    _ = 6 * Real.sqrt x := by
        have : x * (4 / Real.sqrt x) = 4 * Real.sqrt x := by
          have hs0 : Real.sqrt x ≠ 0 := by positivity
          field_simp
          rw [Real.sq_sqrt hx0.le]
        rw [this]; ring
end Formalism.HermitianLattices.GL2PrimeSums
