-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_W_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:37.581558+00:00
-- url     : https://prove2.me/submissions/a617b46b-7867-44d3-b820-1dcc4b939bf7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_out_cases
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_nonneg

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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (N m₀ d : ℕ) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤
      ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n + primeTermWeight x N d := by
  by_cases hd : d = 1
  · subst hd
    linarith [gl2a5s_nonneg hx N 1]
  · have h1 : ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤ primeTermWeight x N d := by
      unfold primeTermWeight
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [mem_filter] at hn ⊢
        have hpp : IsPrimePow n := (mem_filter.1 hn.1).2
        refine ⟨hn.1, ?_⟩
        rcases gl2a5_out_cases m₀ hpp with h | h
        · exact absurd (hn.2.symm.trans h) hd
        · rw [← h]; exact hn.2
      · intro n _ _; exact gl2a5_cn_nonneg hx n
    have h2 : 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n :=
      Finset.sum_nonneg (fun n _ => gl2a5_cn_nonneg hx n)
    linarith
end Formalism.HermitianLattices.GL2PrimeSums
