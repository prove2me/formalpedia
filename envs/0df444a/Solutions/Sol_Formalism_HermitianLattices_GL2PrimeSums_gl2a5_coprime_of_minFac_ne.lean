-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_coprime_of_minFac_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:40.893623+00:00
-- url     : https://prove2.me/submissions/59a19d12-cb6b-42b0-b67a-1f0bacbbeb97

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
theorem _root_.solution {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (h : n.minFac ≠ n'.minFac) : Nat.Coprime n n' := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
  obtain ⟨p', k', hp', hk', rfl⟩ := (isPrimePow_nat_iff n').1 hn'
  rw [hp.pow_minFac hk.ne', hp'.pow_minFac hk'.ne'] at h
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hp').2 h)
end Formalism.HermitianLattices.GL2PrimeSums
