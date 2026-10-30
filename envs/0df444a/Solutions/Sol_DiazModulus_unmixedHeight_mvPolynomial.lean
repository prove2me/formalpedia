-- Prove2me | solution 1 for DiazModulus.unmixedHeight_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T18:17:42.129414+00:00
-- url     : https://prove2.me/submissions/276d4a67-1aea-4177-ae2a-f4bbf777da34

import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_height_le_length_of_mem_associatedPrimes
import Theorems.Thm_DiazModulus_exists_isWeaklyRegular_vanishing

open RingTheory.Sequence IsLocalRing

/-! # Macaulay's unmixedness for `K[X_σ]`, `K` algebraically closed, `σ` finite (the `≤` half)

Let `rs` be weakly regular on `S = K[X_σ]` and `𝔭` an associated prime of `S/(rs)`. Then `𝔭` contains
the annihilator of `S/(rs)`, hence `rs`; choose a maximal ideal `𝔪 ⊇ 𝔭` and put `A = S_𝔪`, a
Noetherian local ring. By the Nullstellensatz (`MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`),
`𝔪` is the vanishing ideal of a point `a`, so `DiazModulus.exists_isWeaklyRegular_vanishing` gives a
weakly regular sequence of length `#σ` in `𝔪`; it localises to a regular sequence in the maximal ideal
of `A` (`IsWeaklyRegular.isRegular_of_isLocalization_of_mem`), and `dim A = ht 𝔪 ≤ dim S = #σ`
(`MvPolynomial.ringKrullDim_of_isNoetherianRing`). In the same way `rs` localises to a regular
sequence in the maximal ideal of `A`. The prime `𝔭A` is an associated prime of `A/(rs)A`, by the
transfer of associated primes along the localisation `S/(rs) → A/(rs)A`
(`Submodule.toLocalizedQuotient'`, `Ideal.localized'_eq_map`), and `ht 𝔭A = ht 𝔭`
(`IsLocalization.height_under`). `DiazModulus.height_le_length_of_mem_associatedPrimes` then gives
`ht 𝔭 = ht 𝔭A ≤ |rs|`. -/

namespace C12_U
open DiazModulus

open MvPolynomial in
/-- At a maximal ideal `𝔪` of `K[X_σ]`, `K` algebraically closed, the local ring `K[X_σ]_𝔪` carries
a regular sequence in its maximal ideal at least as long as its dimension. -/
lemma cmMax {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ] (𝔪 : Ideal (MvPolynomial σ K))
    [h𝔪 : 𝔪.IsMaximal] :
    ∃ zs : List (Localization.AtPrime 𝔪), IsRegular (Localization.AtPrime 𝔪) zs ∧
      (∀ z ∈ zs, z ∈ maximalIdeal (Localization.AtPrime 𝔪)) ∧
      ringKrullDim (Localization.AtPrime 𝔪) ≤ zs.length := by
  obtain ⟨x, hx⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.mp h𝔪
  obtain ⟨zs, hlen, hev, hreg⟩ := DiazModulus.exists_isWeaklyRegular_vanishing (R := K) x
  have hmem : ∀ z ∈ zs, z ∈ 𝔪 := fun z hz => by
    rw [hx, mem_vanishingIdeal_iff]
    rintro y rfl
    exact hev z hz
  refine ⟨zs.map (algebraMap _ _), hreg.isRegular_of_isLocalization_of_mem _ 𝔪 hmem, ?_, ?_⟩
  · simp only [List.mem_map]
    rintro _ ⟨z, hz, rfl⟩
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔪 z).mpr (hmem z hz)
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪, List.length_map, hlen]
    refine (Ideal.height_le_ringKrullDim_of_ne_top h𝔪.ne_top).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- Associated primes of `S ⧸ (rs)` inside `𝔪` localise to associated primes of
`S_𝔪 ⧸ (rs)`, and keep their height. -/
lemma mem_associatedPrimes_atPrime {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime]
    (rs : List S) (𝔭 : Ideal S) (h𝔭 : 𝔭 ∈ associatedPrimes S (S ⧸ Ideal.ofList rs))
    (hle : 𝔭 ≤ 𝔪) :
    𝔭.map (algebraMap S (Localization.AtPrime 𝔪)) ∈ associatedPrimes (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪 ⧸ Ideal.ofList (rs.map (algebraMap S (Localization.AtPrime 𝔪)))) ∧
    (𝔭.map (algebraMap S (Localization.AtPrime 𝔪))).height = 𝔭.height := by
  have := h𝔭.isPrime
  have hd : Disjoint (𝔪.primeCompl : Set S) 𝔭 :=
    Set.disjoint_left.mpr fun a ha h => ha (hle h)
  have hc := IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl
    (Localization.AtPrime 𝔪) this hd
  refine ⟨?_, ?_⟩
  · have key := Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      𝔪.primeCompl ((Ideal.ofList rs).toLocalizedQuotient' (Localization.AtPrime 𝔪) 𝔪.primeCompl
        (Algebra.linearMap S (Localization.AtPrime 𝔪)))
      (𝔭.map (algebraMap S (Localization.AtPrime 𝔪))) (by convert h𝔭 using 1)
    rwa [Ideal.localized'_eq_map, Ideal.map_ofList] at key
  · rw [← IsLocalization.height_under 𝔪.primeCompl]
    exact congrArg Ideal.height hc

end C12_U

open DiazModulus C12_U in
theorem solution {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ] :
    UnmixedHeight (MvPolynomial σ K) := by
  intro rs hrs 𝔭 h𝔭
  have := h𝔭.isPrime
  obtain ⟨𝔪, h𝔪, h𝔭𝔪⟩ := Ideal.exists_le_maximal 𝔭 this.ne_top
  have hrs𝔪 : ∀ r ∈ rs, r ∈ 𝔪 := by
    intro r hr
    apply h𝔭𝔪
    apply h𝔭.annihilator_le
    rw [Submodule.mem_annihilator]
    intro y _
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right s _ (Ideal.subset_span hr)
  have := h𝔪
  have : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance
  obtain ⟨zs, hz, hzm, hdim⟩ := cmMax 𝔪
  obtain ⟨hA, hht⟩ := mem_associatedPrimes_atPrime 𝔪 rs 𝔭 h𝔭 h𝔭𝔪
  have hle := DiazModulus.height_le_length_of_mem_associatedPrimes zs hz hzm hdim _
    (hrs.isRegular_of_isLocalization_of_mem _ 𝔪 hrs𝔪).toIsWeaklyRegular (by
      simp only [List.mem_map]
      rintro _ ⟨r, hr, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔪 r).mpr (hrs𝔪 r hr)) _ hA
  rwa [hht, List.length_map] at hle
