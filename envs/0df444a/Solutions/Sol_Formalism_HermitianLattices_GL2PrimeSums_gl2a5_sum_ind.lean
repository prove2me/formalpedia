-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_sum_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:40.245954+00:00
-- url     : https://prove2.me/submissions/92b235b2-0dd3-40d4-a62d-c5f821d30b46

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
theorem _root_.solution (P : Finset ℕ) (c : ℕ → ℝ) (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] :
    ∑ n ∈ P, ∑ n' ∈ P, c n * c n' * (if A n ∧ B n' then (1 : ℝ) else 0) =
      (∑ n ∈ P.filter A, c n) * (∑ n ∈ P.filter B, c n) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro n' _
  by_cases hA : A n <;> by_cases hB : B n' <;> simp [hA, hB]
end Formalism.HermitianLattices.GL2PrimeSums
