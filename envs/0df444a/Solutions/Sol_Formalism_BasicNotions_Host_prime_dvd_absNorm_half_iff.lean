-- Prove2me | solution 1 for Formalism.BasicNotions.Host.prime_dvd_absNorm_half_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:10.536242+00:00
-- url     : https://prove2.me/submissions/1da7abac-bf6c-4dd4-843e-10b41a7896cb

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_HalfNorm
import Theorems.Thm_Formalism_BasicNotions_Host_mem_ramI_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_UpperTheory_HF_half_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open UpperTheory.HF
open NumberField Ideal
open scoped Pointwise
namespace Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
private theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) : P.LiesOver (span {(p : ℤ)}) :=
  ⟨Ideal.IsMaximal.eq_of_le
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible)
    (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]; exact h)⟩
private theorem dvd_absNorm_of {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P J : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : (p : 𝓞 E) ∈ P) (hJ : P ∣ J) : p ∣ absNorm J := by
  by_contra hn
  obtain ⟨u, v, huv⟩ : IsCoprime (p : 𝓞 E) ((absNorm J : ℕ) : 𝓞 E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).cast
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2
    (huv ▸ P.add_mem (P.mul_mem_left u h) (P.mul_mem_left v (Ideal.le_of_dvd hJ (Ideal.absNorm_mem J)))))
end Formalism.BasicNotions.Host
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal
open scoped Pointwise
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) : p ∣ absNorm H.𝔟 ↔ p ∣ H.QS * H.q := by
  have hs := (UpperTheory.HF.half_supp H.toHostAx H.𝔟 H.𝔟_spec.1 H.𝔟_spec.2).1
  constructor
  · intro h
    obtain ⟨P, hP, hu, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h
    haveI := hP.isPrime
    obtain ⟨l, hl, ho⟩ := (hs P).1.1 (Or.inl hd)
    have hlp : l.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
    have e : span {(l : ℤ)} = span {(p : ℤ)} := ho.over.trans hu
    have : p ∣ l := by
      have := Ideal.mem_span_singleton.1 (e ▸ Ideal.mem_span_singleton_self (l : ℤ))
      exact_mod_cast this
    rw [(Nat.prime_dvd_prime_iff_eq hp hlp).1 this]
    exact (H.mem_ramI_iff hlp).1 hl
  · intro h
    have h1 : p ∣ absNorm (span {(p : 𝓞 H.E)}) := by
      rw [Ideal.absNorm_span_natCast]
      exact dvd_pow_self _ Module.finrank_pos.ne'
    obtain ⟨P, hP, -, hd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ h1
    haveI := hP.isPrime
    have hm : (p : 𝓞 H.E) ∈ P := Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
    rcases (hs P).1.2 ⟨p, (H.mem_ramI_iff hp).2 h, liesOver_of_mem hp P hm⟩ with h2 | h2
    · exact dvd_absNorm_of hp P _ hm h2
    · have hm' : (p : 𝓞 H.E) ∈ H.toHostRaw.conj • P := by
        have := Ideal.smul_mem_pointwise_smul H.toHostRaw.conj _ _ hm
        rwa [show H.toHostRaw.conj • (p : 𝓞 H.E) = p from map_natCast (MulSemiringAction.toRingHom _ (𝓞 H.E) H.toHostRaw.conj) p] at this
      exact dvd_absNorm_of hp _ _ hm' h2
end Formalism.BasicNotions.Host
