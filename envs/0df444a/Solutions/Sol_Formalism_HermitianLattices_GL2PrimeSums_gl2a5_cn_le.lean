-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_cn_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:39.925181+00:00
-- url     : https://prove2.me/submissions/dde5ef89-85e2-47e0-9447-f7cd06a12ce1

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
theorem _root_.solution (x : ℝ) (n : ℕ) : cn x n ≤ Λ n := by
  unfold cn
  exact mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)
end Formalism.HermitianLattices.GL2PrimeSums
