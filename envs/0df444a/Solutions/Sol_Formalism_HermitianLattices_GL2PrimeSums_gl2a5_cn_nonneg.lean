-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_cn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:22.189907+00:00
-- url     : https://prove2.me/submissions/4122b9d8-2873-4045-ba8e-96539e3ecbd0

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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cn x n := by
  unfold cn
  exact mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (by positivity))
end Formalism.HermitianLattices.GL2PrimeSums
