-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_outPart_primePow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:55.558339+00:00
-- url     : https://prove2.me/submissions/a6711c9c-ff37-4368-ae4d-a7fec155781b

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
theorem _root_.solution (m₀ : ℕ) {n : ℕ} (hn : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k ∧ n.minFac = p ∧
      outPart m₀ n = if (¬ p ∣ m₀ ∧ Odd k) then p else 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  refine ⟨p, k, hp, hk, rfl, hp.pow_minFac hk.ne', ?_⟩
  unfold outPart
  rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.filter_singleton]
  have : (p ^ k).factorization p = k := by
    rw [hp.factorization_pow]; simp
  rw [this]
  split_ifs <;> simp
end Formalism.HermitianLattices.GL2PrimeSums
