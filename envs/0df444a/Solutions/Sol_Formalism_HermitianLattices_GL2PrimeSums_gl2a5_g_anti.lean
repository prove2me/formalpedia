-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_g_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:38.159983+00:00
-- url     : https://prove2.me/submissions/1349b4b0-5ad0-469d-901d-7d805ad9cd31

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
theorem _root_.solution {n : ℕ} (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ Real.log n / (n : ℝ) ^ 2 := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ n := by linarith [Real.exp_one_lt_d9]
  have h1 : Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ Real.log n / n := by
    apply Real.log_div_self_antitoneOn (by simpa using he)
    · show Real.exp 1 ≤ _
      push_cast; linarith
    · push_cast; linarith
  have h2 : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 / n := by
    apply one_div_le_one_div_of_le (by linarith)
    push_cast; linarith
  have h3 : 0 ≤ Real.log n / n := by
    have := Real.log_natCast_nonneg n
    positivity
  have h4 := mul_le_mul h1 h2 (by positivity) h3
  calc _ = Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) := by
        rw [sq, div_mul_div_comm, mul_one]
    _ ≤ _ := h4
    _ = _ := by rw [sq, div_mul_div_comm, mul_one]
end Formalism.HermitianLattices.GL2PrimeSums
