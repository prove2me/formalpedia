-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Mu.mu_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:15:48.969172+00:00
-- url     : https://prove2.me/submissions/a20e318b-25ca-4cec-8916-ae559e29e941

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.Mu
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (η : L) (hη : IsPrimitiveRoot η p) :
    ((p : ℤ) : 𝓞 L) ∈ Q ^ (p - 1) := by
  have hp0 : 0 < p := hp.out.pos
  have hint : IsIntegral ℤ η := hη.isIntegral hp0
  let η' : 𝓞 L := ⟨η, hint⟩
  have hmapη : algebraMap (𝓞 L) L η' = η := rfl
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := by
    first
      | exact FaithfulSMul.algebraMap_injective (𝓞 L) L
      | exact NumberField.RingOfIntegers.coe_injective
  have hη' : IsPrimitiveRoot η' p := by
    refine ⟨hinj ?_, fun l hl => hη.dvd_of_pow_eq_one l ?_⟩
    · rw [map_pow, hmapη, map_one]
      exact hη.pow_eq_one
    · rw [← hmapη, ← map_pow, hl, map_one]
  have hprod : ((p : ℤ) : 𝓞 L) = ∏ μ ∈ primitiveRoots p (𝓞 L), (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hη', Polynomial.eval_prod] at h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
    rw [Int.cast_natCast, ← h1]
  have hmemQ : ((p : ℤ) : 𝓞 L) ∈ Q := by
    have hover : span {(p : ℤ)} = Ideal.under ℤ Q := Ideal.LiesOver.over
    have h1 : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [← hover]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap, algebraMap_int_eq, eq_intCast] at h1
    exact h1
  rw [hprod] at hmemQ
  obtain ⟨μ0, hμ0mem, hμ0Q⟩ : ∃ μ ∈ primitiveRoots p (𝓞 L), 1 - μ ∈ Q := by
    first
      | exact Ideal.IsPrime.prod_mem_iff.mp hmemQ
      | exact (Ideal.IsPrime.prod_mem_iff_exists_mem ‹Q.IsPrime›).mp hmemQ
      | exact (Ideal.IsPrime.prod_mem_iff ‹Q.IsPrime›).1 hmemQ
  have hall : ∀ μ ∈ primitiveRoots p (𝓞 L), 1 - μ ∈ Q := by
    intro μ hμ
    have hμ0p : IsPrimitiveRoot μ0 p := (mem_primitiveRoots hp0).mp hμ0mem
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp0).mp hμ
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    obtain ⟨i, -, hi⟩ := hμ0p.eq_pow_of_pow_eq_one hμp.pow_eq_one
    rw [← hi]
    have hd : 1 - μ0 ∣ 1 - μ0 ^ i := by simpa [one_pow] using sub_dvd_pow_sub_pow 1 μ0 i
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact Ideal.mul_mem_right c Q hμ0Q
  rw [hprod]
  have h2 := Ideal.prod_mem_prod (I := fun _ => Q) hall
  rw [Finset.prod_const, IsPrimitiveRoot.card_primitiveRoots hη', Nat.totient_prime hp.out] at h2
  exact h2
end Formalism.FrobeniusOrbits.Mu
