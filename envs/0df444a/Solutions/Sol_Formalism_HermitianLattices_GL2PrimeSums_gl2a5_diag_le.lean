-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:32.515801+00:00
-- url     : https://prove2.me/submissions/45cfeb28-468b-437b-8689-b85d1e762111

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_split
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_small
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_large

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
theorem _root_.solution (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) {x : ℝ}
    (hx : 3 ≤ x) (N : ℕ) :
    ∑ p ∈ Icc 1 N, (primeTermWeight x N p) ^ 2 ≤ 62 * x * Real.log x := by
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have h1 := gl2a5_split (fun p => (primeTermWeight x N p) ^ 2) (fun p => by positivity) ⌊x⌋₊ N
  have h2 := gl2a5_diag_small hψ he N
  have h3 := gl2a5_diag_large hψ hx N
  linarith
end Formalism.HermitianLattices.GL2PrimeSums
