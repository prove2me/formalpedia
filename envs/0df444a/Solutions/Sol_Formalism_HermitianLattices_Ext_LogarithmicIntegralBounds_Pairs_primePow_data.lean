-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.primePow_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:10.752375+00:00
-- url     : https://prove2.me/submissions/6406bf0f-775e-4174-8432-8925553c4886

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
theorem _root_.solution {n : ℕ} (h : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ k ≠ 0 ∧ n = p ^ k ∧ n.minFac = p ∧ n.factorization n.minFac = k := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
  have hm : (p ^ k).minFac = p := hp.pow_minFac hk.ne'
  refine ⟨p, k, hp, hk.ne', rfl, hm, ?_⟩
  rw [hm, factorization_prime_pow_self p k hp]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
