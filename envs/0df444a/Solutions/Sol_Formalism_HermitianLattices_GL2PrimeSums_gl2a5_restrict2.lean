-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_restrict2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:32.697954+00:00
-- url     : https://prove2.me/submissions/b0dd6f94-3033-4d30-9420-731cfcac224a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_restrict

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
theorem _root_.solution (x : ℝ) (N : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' * G n n' =
      ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' * G n n' := by
  have h1 : ∀ (S : Finset ℕ) (n : ℕ), ∑ n' ∈ S, cn x n * cn x n' * G n n' =
      cn x n * ∑ n' ∈ S, cn x n' * G n n' := by
    intro S n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n' _; ring
  simp only [h1]
  rw [gl2a5_restrict]
  apply Finset.sum_congr rfl; intro n _
  rw [gl2a5_restrict]
end Formalism.HermitianLattices.GL2PrimeSums
