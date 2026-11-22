-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:12.287605+00:00
-- url     : https://prove2.me/submissions/b1f978e6-8274-449c-8d35-bba2054da50c

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
theorem _root_.solution (x : ℝ) (N : ℕ) {p : ℕ} (hp : ¬ p.Prime) : primeTermWeight x N p = 0 := by
  unfold primeTermWeight
  have : (primesLeFinset N).filter (fun n => n.minFac = p) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro n hn hmf
    simp only [primesLeFinset, mem_filter] at hn
    exact hp (hmf ▸ Nat.minFac_prime hn.2.ne_one)
  rw [this, Finset.sum_empty]
end Formalism.HermitianLattices.GL2PrimeSums
