-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:26.592978+00:00
-- url     : https://prove2.me/submissions/414071f1-6dd6-4e09-a134-c09e6295ac7a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ primeTermWeight x N p :=
  Finset.sum_nonneg (fun _ _ => gl2a5_cn_nonneg hx _)
end Formalism.HermitianLattices.GL2PrimeSums
