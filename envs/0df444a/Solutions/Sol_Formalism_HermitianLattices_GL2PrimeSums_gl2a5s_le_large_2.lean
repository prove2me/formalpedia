-- Prove2me | solution 2 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.405369+00:00
-- url     : https://prove2.me/submissions/38f1f0b4-54b8-4e92-8369-28d77f861bcf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le

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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    primeTermWeight x N p ≤ 2 * x * (Real.log p / p) := by
  have h := gl2a5s_le hx N hp 0
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_add, pow_one]
  ring
end Formalism.HermitianLattices.GL2PrimeSums
