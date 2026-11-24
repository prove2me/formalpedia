-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_primes_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:48.540884+00:00
-- url     : https://prove2.me/submissions/e3eda627-a4d0-4676-b333-bced79c9b044

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_prime_norm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_prime_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
open UniqueFactorizationMonoid
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ s : Finset (Ideal (𝓞 K)), s.card ≤ finrank ℚ K ∧
      ∀ Q : Ideal (𝓞 K), Q.IsPrime → (p : 𝓞 K) ∈ Q → Q ∈ s := by
  classical
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hI : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  refine ⟨(normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset, ?_, ?_⟩
  · refine (Multiset.toFinset_card_le _).trans ?_
    have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
      rw [Ideal.absNorm_span_singleton]
      have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K := by
        have h := Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)
        rw [RingOfIntegers.rank] at h
        simpa using h
      rw [this]; simp [Int.natAbs_pow]
    have h1 : ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod =
        p ^ finrank ℚ K := by
      rw [← hnp, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
    have h2 : p ^ Multiset.card ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm) ≤
        ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod := by
      apply Multiset.pow_card_le_prod
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨hQp, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hQ
      have hpQ : (p : 𝓞 K) ∈ Q := hle (Ideal.mem_span_singleton_self _)
      have hQ0 : Q ≠ ⊥ := fun h => hp0 (by rw [h] at hpQ; exact hpQ)
      obtain ⟨q, k, hq, hk, _, hqQ, hN⟩ := s5a4_prime_norm Q hQp hQ0
      rw [hN, s5a4_prime_unique Q hQp p q hp hq hpQ hqQ]
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ k := Nat.pow_le_pow_right hq.pos hk
    rw [h1, Multiset.card_map] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  · intro Q hQ hpQ
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI]
    exact ⟨hQ, (Ideal.span_singleton_le_iff_mem Q).mpr hpQ⟩
end Formalism.HermitianLatticeCounting.P
