-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:38.410693+00:00
-- url     : https://prove2.me/submissions/b907479d-fdc6-4df3-986e-0c921242f265

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_tele

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
theorem _root_.solution (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (a0 L : ℕ) :
    ∑ a ∈ Ioc a0 L, r ^ a ≤ 2 * r ^ (a0 + 1) := by
  have := gl2a5_tele (fun a => r ^ a) (fun a => 2 * r ^ (a + 1)) a0 (by
    intro n _
    have : 0 ≤ r ^ (n + 1) := pow_nonneg h0 _
    simp only [pow_succ] at this ⊢
    nlinarith) (fun n => by positivity) L
  exact this
end Formalism.HermitianLattices.GL2PrimeSums
