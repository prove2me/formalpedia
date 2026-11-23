-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:11.232596+00:00
-- url     : https://prove2.me/submissions/54488651-be34-4b06-98b7-eb6232745f25

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Pairs
private lemma factorization_prime_pow_self (p k : ℕ) (hp : p.Prime) : (p ^ k).factorization p = k := by
  simp [Nat.factorization_pow, hp.factorization_self]
end Pairs
open Pairs
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
theorem _root_.solution (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    soutPart m₀ (p ^ k) = if Odd k ∧ ¬ p ∣ m₀ then p else 1 := by
  unfold soutPart
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton, factorization_prime_pow_self p k hp]
  split_ifs <;> simp
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
