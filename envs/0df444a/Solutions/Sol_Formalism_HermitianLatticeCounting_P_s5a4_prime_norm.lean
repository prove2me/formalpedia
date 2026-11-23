-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_prime_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:56.870817+00:00
-- url     : https://prove2.me/submissions/79e839d6-5002-4e13-b890-b18408c4bd1c

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ k ≤ finrank ℚ K ∧ (p : 𝓞 K) ∈ Q ∧
      Ideal.absNorm Q = p ^ k := by
  have hN0 : Ideal.absNorm Q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hQ0
  have hN1 : Ideal.absNorm Q ≠ 1 := fun h => hQ.ne_top (Ideal.absNorm_eq_one_iff.mp h)

  have hex : ∀ m : ℕ, m ≠ 0 → (m : 𝓞 K) ∈ Q → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd ((Ideal.eq_top_iff_one Q).mpr (by simpa using h)) hQ.ne_top
    | prime p hp => intro _ h; exact ⟨p, hp, h⟩
    | mul a b iha ihb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases hQ.mem_or_mem h with h | h
      · exact iha (left_ne_zero_of_mul hab) h
      · exact ihb (right_ne_zero_of_mul hab) h
  obtain ⟨p, hp, hpQ⟩ := hex _ hN0 (Ideal.absNorm_mem Q)
  have hle : Ideal.span {(p : 𝓞 K)} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hpQ
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K := by
      have h := Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)
      rw [RingOfIntegers.rank] at h
      simpa using h
    rw [this]; simp [Int.natAbs_pow]
  rw [hnp] at hdvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨p, k, hp, ?_, hk, hpQ, hkeq⟩
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, pow_zero] at hkeq; exact absurd hkeq hN1
  · exact h
end Formalism.HermitianLatticeCounting.P
