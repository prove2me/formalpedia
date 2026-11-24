-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_R_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:04.886205+00:00
-- url     : https://prove2.me/submissions/30a8a64b-14b9-4864-8a2d-f1a2d5cfec27

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_out_one
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_small_prime_factor_sum_bound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_square_terms_sum_le_sqrt

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
    (hx : Real.exp 1 ≤ x) (N m₀ : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (h : ∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ Y) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n ≤
      Y * (3 * Real.log x) + 6 * Real.sqrt x := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 := small_prime_factor_sum_bound hx N m₀ Y hY h
  have h2 := square_terms_sum_le_sqrt hψ hx1 N
  have h3 := Finset.sum_union_inter (s₁ := (primesLeFinset N).filter (fun n => n.minFac ∣ m₀))
    (s₂ := (primesLeFinset N).filter (fun n => IsSquare n)) (f := cn x)
  have h4 : 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀) ∩
      (primesLeFinset N).filter (fun n => IsSquare n), cn x n :=
    Finset.sum_nonneg (fun n _ => gl2a5_cn_nonneg (by linarith) n)
  have h5 : ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n ≤
      ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀) ∪
        (primesLeFinset N).filter (fun n => IsSquare n), cn x n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [mem_filter] at hn
      have hpp : IsPrimePow n := (mem_filter.1 hn.1).2
      rw [mem_union, mem_filter, mem_filter]
      rcases gl2a5_out_one m₀ hpp hn.2 with hd | ⟨m, hm⟩
      · exact Or.inl ⟨hn.1, hd⟩
      · exact Or.inr ⟨hn.1, ⟨m, by rw [hm, sq]⟩⟩
    · intro n _ _; exact gl2a5_cn_nonneg (by linarith) n
  linarith
end Formalism.HermitianLattices.GL2PrimeSums
