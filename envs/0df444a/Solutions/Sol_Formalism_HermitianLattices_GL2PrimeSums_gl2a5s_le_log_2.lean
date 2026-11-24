-- Prove2me | solution 2 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:20.337346+00:00
-- url     : https://prove2.me/submissions/8a21c067-5007-4dac-8d48-ee37f7659af6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_not_prime
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_small
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_large

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
theorem _root_.solution {x : ℝ} (hx : Real.exp 1 ≤ x) (N p : ℕ) :
    primeTermWeight x N p ≤ 3 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  by_cases hp : p.Prime
  · rcases le_or_gt (p : ℝ) x with hpx | hpx
    · have := gl2a5s_le_small hx1 N hp
      have h2 : Real.log p ≤ Real.log x := Real.log_le_log (by exact_mod_cast hp.pos) hpx
      linarith
    · have := gl2a5s_le_large (by linarith : (0 : ℝ) ≤ x) N hp
      have h2 : Real.log p / p ≤ Real.log x / x :=
        Real.log_div_self_antitoneOn (by simpa using hx) (by simpa using hx.trans hpx.le) hpx.le
      have h3 : 2 * x * (Real.log p / p) ≤ 2 * x * (Real.log x / x) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : 2 * x * (Real.log x / x) = 2 * Real.log x := by field_simp
      linarith
  · rw [gl2a5s_not_prime x N hp]; positivity
end Formalism.HermitianLattices.GL2PrimeSums
