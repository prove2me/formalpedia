-- Prove2me | solution 1 for CyclotomicEulerSystem.congruence_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:56:35.888986+00:00
-- url     : https://prove2.me/submissions/239f4ca9-af66-4ef6-b7c2-b93c90e7337a

import Definitions.Def_CyclotomicEulerSystem_defs

open NumberField CyclotomicEulerSystem

theorem solution (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ) (n l : ℕ)
    (hn : Squarefree n) (hl : l.Prime) (hln : ¬ l ∣ n)
    (P : Ideal (𝓞 (cycField ζ (n * l)))) (hP : P.IsPrime)
    (hlP : (l : 𝓞 (cycField ζ (n * l))) ∈ P)
    (x y : 𝓞 (cycField ζ (n * l)))
    (hx : ((x : cycField ζ (n * l)) : ℂ) = alpha ζ (n * l))
    (hy : ((y : cycField ζ (n * l)) : ℂ) = alpha ζ n) :
    x - y ∈ P := by
  let K := cycField ζ (n * l)
  let f : 𝓞 K →+* ℂ := (algebraMap K ℂ).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := (algebraMap K ℂ).injective.comp
    RingOfIntegers.coe_injective
  have hcompat := hζ.2 n l hn hl.squarefree (hl.coprime_iff_not_dvd.mpr hln).symm
  have hroot := (hζ.1 l hl.squarefree).pow_eq_one
  have hpow : (1 - x) ^ l = (1 - y) ^ l := by
    apply hf
    simp only [map_pow, map_sub, map_one, f, RingHom.comp_apply,
      show algebraMap K ℂ (algebraMap (𝓞 K) K x) = alpha ζ (n * l) from hx,
      show algebraMap K ℂ (algebraMap (𝓞 K) K y) = alpha ζ n from hy,
      alpha, sub_sub_cancel, hcompat, mul_pow, hroot, mul_one]
  let : P.IsPrime := hP
  let : Fact l.Prime := ⟨hl⟩
  have hz : (l : (𝓞 K) ⧸ P) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hlP)
  let : CharP ((𝓞 K) ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl).mpr hz
  have hq := congrArg (Ideal.Quotient.mk P) hpow
  simp only [map_pow, map_sub, map_one, sub_pow_char] at hq
  have hxy : (Ideal.Quotient.mk P x - Ideal.Quotient.mk P y) ^ l = 0 := by
    rw [sub_pow_char]
    linear_combination -hq
  have heq : Ideal.Quotient.mk P x - Ideal.Quotient.mk P y = 0 :=
    eq_zero_of_pow_eq_zero hxy
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_sub] using heq)
