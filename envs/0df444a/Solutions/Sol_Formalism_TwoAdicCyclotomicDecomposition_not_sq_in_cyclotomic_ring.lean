-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.not_sq_in_cyclotomic_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:07.416563+00:00
-- url     : https://prove2.me/submissions/4abb2ed0-c600-49c2-8631-0bce768bbddf

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ N)
    (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) (X : 𝓞 K) (hX : X ^ 2 = ((p * m : ℤ) : 𝓞 K)) : False := by
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  have he : P.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpN
  have hp0 : (span {(p : ℤ)}) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  have he' : (span {(p : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp0, he]
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := by
    have := (Ideal.over_def P (span {(p : ℤ)}))
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← this]; exact mem_span_singleton_self _
    simpa using h1
  have hXP : X ∈ P := by
    apply (inferInstance : P.IsPrime).mem_of_pow_mem 2
    rw [hX, Int.cast_mul]
    exact P.mul_mem_right _ hpP
  have hX2 : X ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hXP 2
  obtain ⟨s, t, hst⟩ : IsCoprime m (p : ℤ) := by
    exact ((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hm).symm
  have hp2 : ((p : ℤ) : 𝓞 K) ∈ P ^ 2 := by
    have : ((p : ℤ) : 𝓞 K) = (s : 𝓞 K) * X ^ 2 + (t : 𝓞 K) * (((p : ℤ) : 𝓞 K) * ((p : ℤ) : 𝓞 K)) := by
      rw [hX]
      have h' : ((s * m + t * p : ℤ) : 𝓞 K) = 1 := by rw [hst, Int.cast_one]
      push_cast at h' ⊢
      linear_combination (-(p : 𝓞 K)) * h'
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hX2) (Ideal.mul_mem_left _ _ ?_)
    rw [pow_two]; exact Ideal.mul_mem_mul hpP hpP
  have hle : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ 2 := by
    rw [Ideal.map_span, span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    simpa using hp2
  have hB : BddAbove {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} := by
    by_contra hB
    have := Nat.sSup_of_not_bddAbove hB
    unfold Ideal.ramificationIdx' at he'
    omega
  have := le_csSup hB (show 2 ∈ {k | map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≤ P ^ k} from hle)
  unfold Ideal.ramificationIdx' at he'
  omega
end Formalism.TwoAdicCyclotomicDecomposition
