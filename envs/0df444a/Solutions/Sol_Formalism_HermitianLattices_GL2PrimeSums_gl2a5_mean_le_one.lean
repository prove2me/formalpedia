-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_mean_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:39.476699+00:00
-- url     : https://prove2.me/submissions/603ca76f-e260-47b4-8c4e-d63a12ce4db5

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
theorem _root_.solution (PPs : Finset ℕ) (a : ℤ) :
    |(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by
  rw [abs_div, Nat.abs_cast]
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q ∈ PPs, |(jacobiSym a q : ℝ)| ≤ ∑ q ∈ PPs, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro q _
        rcases jacobiSym.trichotomy a q with h | h | h <;> rw [h] <;> simp
    _ = PPs.card := by simp
end Formalism.HermitianLattices.GL2PrimeSums
