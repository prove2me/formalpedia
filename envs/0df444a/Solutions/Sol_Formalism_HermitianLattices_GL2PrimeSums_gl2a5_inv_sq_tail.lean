-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_inv_sq_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:38.737343+00:00
-- url     : https://prove2.me/submissions/d6612e12-3c92-4cca-905b-31d1c5d69b80

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
theorem _root_.solution (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ n ∈ Ioc K M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  apply gl2a5_tele (fun n => (1 : ℝ) / (n : ℝ) ^ 2) (fun n => 1 / (n : ℝ)) K _ (fun n => by positivity) M
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  push_cast
  rw [div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
end Formalism.HermitianLattices.GL2PrimeSums
