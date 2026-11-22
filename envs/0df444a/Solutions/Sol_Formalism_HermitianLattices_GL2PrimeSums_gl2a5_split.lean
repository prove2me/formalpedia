-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:10.207918+00:00
-- url     : https://prove2.me/submissions/0d56efdf-a1b5-4119-85c9-b154bc83eded

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound

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
theorem _root_.solution (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (K N : ℕ) :
    ∑ n ∈ Icc 1 N, f n ≤ ∑ n ∈ Icc 1 K, f n + ∑ n ∈ Ioc K N, f n := by
  rw [← Finset.sum_union]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ioc, mem_Icc, mem_union] at hn ⊢
      omega
    · intro n _ _; exact hf n
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [mem_Ioc, mem_Icc] at hn hn'
    omega
end Formalism.HermitianLattices.GL2PrimeSums
