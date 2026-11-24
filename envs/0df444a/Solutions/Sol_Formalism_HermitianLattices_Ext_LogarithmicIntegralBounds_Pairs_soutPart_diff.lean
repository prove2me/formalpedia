-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:22.011289+00:00
-- url     : https://prove2.me/submissions/813c1b21-d8b3-4e4f-9be6-6abfad20b449

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_prime_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_mul_of_coprime
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_primePow_data
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
private lemma tPart_prime_pow_eq_soutPart (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    tPart m₀ (p ^ k) = soutPart m₀ (p ^ k) := by
  rw [soutPart_prime_pow m₀ p k hp hk]
  unfold tPart
  rw [hp.pow_minFac hk, factorization_prime_pow_self p k hp]
  rcases Nat.even_or_odd k with h1 | h1
  · have h1' : ¬ Odd k := Nat.not_odd_iff_even.2 h1
    simp [h1, h1']
  · have h1' : ¬ Even k := Nat.not_even_iff_odd.2 h1
    by_cases h2 : p ∣ m₀ <;> simp [h1, h1', h2]
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
theorem _root_.solution {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac ≠ n'.minFac) :
    soutPart m₀ (n * n') = tPart m₀ n * tPart m₀ n' := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p ≠ q := fun hpq => he (hm.trans (hpq.trans hm'.symm))
  have hcop : (p ^ k).Coprime (q ^ k') := Nat.Coprime.pow k k' ((Nat.coprime_primes hp hq).2 hpq)
  rw [soutPart_mul_of_coprime m₀ _ _ hcop, tPart_prime_pow_eq_soutPart m₀ p k hp hk, tPart_prime_pow_eq_soutPart m₀ q k' hq hk']
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
