-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.549298+00:00
-- url     : https://prove2.me/submissions/cf02ac0a-fd39-4f6f-8a82-a3f66b3717a4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_zero

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
theorem _root_.solution (x : ℝ) (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, cn x n * F n = ∑ n ∈ primesLeFinset N, cn x n * F n := by
  unfold primesLeFinset
  symm
  apply Finset.sum_filter_of_ne
  intro n _ hne
  by_contra hpp
  exact hne (by rw [gl2a5_cn_zero x hpp, zero_mul])
end Formalism.HermitianLattices.GL2PrimeSums
