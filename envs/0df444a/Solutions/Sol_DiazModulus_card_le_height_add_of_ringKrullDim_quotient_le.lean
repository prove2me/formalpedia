-- Prove2me | solution 1 for DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:39.731059+00:00
-- url     : https://prove2.me/submissions/a2f1d4f0-23f8-417f-ac23-cca69bbf6767

import Mathlib
import Theorems.Thm_DiazModulus_exists_isRegular_quotient_ofList
import Theorems.Thm_DiazModulus_exists_isWeaklyRegular_vanishing
import Theorems.Thm_DiazModulus_length_le_ringKrullDim_quotient_of_mem_associatedPrimes

open RingTheory.Sequence IsLocalRing

/-! # `|σ| ≤ ht 𝔭 + dim K[X_σ]/𝔭` for a prime of a polynomial ring over an algebraically closed field

Localise at a maximal ideal `𝔪 ⊇ 𝔭`, `𝔪 = (X − a)`; the imported `exists_isWeaklyRegular_vanishing` gives a regular
sequence of length `|σ|` in `A = K[X_σ]_𝔪`. Inside the prime `𝔓 = 𝔭A` (height `ht 𝔭`, finite) take a weakly regular
list `ps` that cannot be extended; its length is at most `ht 𝔭` (grade ≤ height, through
`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` at `𝔓`), and by prime avoidance
(`biUnion_associatedPrimes_eq_compl_regular`) `𝔓` lies in an associated prime `𝔮` of `A/(ps)`. The imported
`exists_isRegular_quotient_ofList` gives a regular sequence `ts` on `A/(ps)` with `|σ| ≤ |ts| + |ps|`, and the
imported `length_le_ringKrullDim_quotient_of_mem_associatedPrimes` bounds `|ts| ≤ dim A/𝔮 ≤ dim A/𝔓 ≤ dim K[X_σ]/𝔭`
(comap along the localisation is strictly monotone). -/

namespace C13_H3
open DiazModulus

/-- Grade ≤ height: a weakly regular list inside a prime `𝔭` has length at most `ht 𝔭`. -/
theorem length_le_height_of_isWeaklyRegular {S : Type*} [CommRing S] [IsNoetherianRing S]
    (𝔭 : Ideal S) [𝔭.IsPrime] (rs : List S) (hrs : IsWeaklyRegular S rs) (hmem : ∀ r ∈ rs, r ∈ 𝔭) :
    (rs.length : ℕ∞) ≤ 𝔭.height := by
  let B := Localization.AtPrime 𝔭
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing 𝔭.primeCompl _ inferInstance
  have hreg : IsRegular B (rs.map (algebraMap S B)) := hrs.isRegular_of_isLocalization_of_mem B 𝔭 hmem
  have key := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 B, List.length_map] at key
  have hnt : Nontrivial (B ⧸ Ideal.ofList (rs.map (algebraMap S B))) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    intro htop
    exact hreg.2 (by rw [htop, smul_eq_mul, Ideal.mul_top])
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Ideal.ofList (rs.map (algebraMap S B))) :=
    ringKrullDim_nonneg_of_nontrivial
  have : ((rs.length : ℕ∞) : WithBot ℕ∞) ≤ (𝔭.height : WithBot ℕ∞) := by
    rw [← key]
    calc ((rs.length : ℕ∞) : WithBot ℕ∞) = 0 + (rs.length : WithBot ℕ∞) := by simp
      _ ≤ _ := add_le_add_left h0 _
  exact_mod_cast this

/-- In a Noetherian ring, a prime `𝔭` of finite height contains a weakly regular list that
cannot be extended inside `𝔭`. -/
theorem exists_maximal_isWeaklyRegular {S : Type*} [CommRing S] [IsNoetherianRing S]
    (𝔭 : Ideal S) [𝔭.IsPrime] (hfin : 𝔭.height ≠ ⊤) :
    ∃ ps : List S, IsWeaklyRegular S ps ∧ (∀ r ∈ ps, r ∈ 𝔭) ∧
      ∀ x ∈ 𝔭, ¬ IsSMulRegular (S ⧸ (Ideal.ofList ps • (⊤ : Submodule S S))) x := by
  by_contra h
  push Not at h
  have hall : ∀ n : ℕ, ∃ ps : List S, ps.length = n ∧ IsWeaklyRegular S ps ∧ ∀ r ∈ ps, r ∈ 𝔭 := by
    intro n
    induction n with
    | zero => exact ⟨[], rfl, IsWeaklyRegular.nil S S, by simp⟩
    | succ n ih =>
      obtain ⟨ps, hlen, hreg, hmem⟩ := ih
      obtain ⟨x, hx𝔭, hxreg⟩ := h ps hreg hmem
      refine ⟨ps ++ [x], by simp [hlen], ?_, ?_⟩
      · exact (isWeaklyRegular_append_iff S ps [x]).mpr
          ⟨hreg, (isWeaklyRegular_singleton_iff _ x).mpr hxreg⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hmem r hr
        · rw [List.mem_singleton.mp hr]; exact hx𝔭
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨ps, hlen, hreg, hmem⟩ := hall (m + 1)
  have := length_le_height_of_isWeaklyRegular 𝔭 ps hreg hmem
  rw [hlen, ← hm] at this
  exact absurd (ENat.natCast_le_natCast.mp this) (by omega)

/-- The Krull dimension of `A ⧸ 𝔓` for a localization `A` of `R` is at most that of
`R ⧸ 𝔓 ∩ R`. -/
theorem ringKrullDim_quotient_le_of_isLocalization {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]
    (T : Submonoid S) [IsLocalization T A] (P : Ideal A) :
    ringKrullDim (A ⧸ P) ≤ ringKrullDim (S ⧸ P.comap (algebraMap S A)) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let f : PrimeSpectrum.zeroLocus (R := A) P → PrimeSpectrum.zeroLocus (R := S) (P.comap (algebraMap S A)) :=
    fun Q => ⟨PrimeSpectrum.comap (algebraMap S A) Q.1, by
      have hQ : (P : Set A) ⊆ Q.1.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp Q.2
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun x hx => hQ hx)⟩
  apply Order.krullDim_le_of_strictMono f
  intro Q₁ Q₂ hlt
  have hinj := PrimeSpectrum.localization_comap_injective A T
  have hle : PrimeSpectrum.comap (algebraMap S A) Q₁.1 ≤ PrimeSpectrum.comap (algebraMap S A) Q₂.1 :=
    fun x hx => hlt.le hx
  refine lt_of_le_of_ne hle ?_
  intro heq
  exact hlt.ne (Subtype.ext (hinj (congrArg Subtype.val heq)))
end C13_H3

open DiazModulus C13_H3 in
theorem solution {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (𝔭 : Ideal (MvPolynomial σ K)) (h𝔭 : 𝔭.IsPrime) (e : ℕ)
    (he : ringKrullDim (MvPolynomial σ K ⧸ 𝔭) ≤ e) :
    (Nat.card σ : ℕ∞) ≤ 𝔭.height + e := by
  have := h𝔭
  classical
  -- a maximal ideal over `𝔭` and its local ring
  obtain ⟨𝔪, h𝔪, h𝔭𝔪⟩ := Ideal.exists_le_maximal 𝔭 h𝔭.ne_top
  let A := Localization.AtPrime 𝔪
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance
  -- the regular sequence `X − a` at `𝔪`, of length `#σ`
  obtain ⟨a, ha⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp h𝔪
  obtain ⟨zs, hzlen, hzev, hzreg⟩ := exists_isWeaklyRegular_vanishing (R := K) a
  have hzmem : ∀ z ∈ zs, z ∈ 𝔪 := fun z hz => by
    rw [ha, MvPolynomial.mem_vanishingIdeal_iff]
    rintro y rfl
    exact hzev z hz
  have hz' : IsRegular A (zs.map (algebraMap _ A)) := hzreg.isRegular_of_isLocalization_of_mem A 𝔪 hzmem
  have hzm' : ∀ z ∈ zs.map (algebraMap _ A), z ∈ maximalIdeal A := by
    simp only [List.mem_map]
    rintro _ ⟨z, hz, rfl⟩
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A 𝔪 z).mpr (hzmem z hz)
  -- the prime `𝔓 = 𝔭 A`
  have hdisj : Disjoint (𝔪.primeCompl : Set (MvPolynomial σ K)) 𝔭 :=
    Set.disjoint_left.mpr fun x hx h => hx (h𝔭𝔪 h)
  let 𝔓 : Ideal A := 𝔭.map (algebraMap _ A)
  have h𝔓 : 𝔓.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl A 𝔭 h𝔭 hdisj
  have hcomap : 𝔓.under (MvPolynomial σ K) = 𝔭 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔪.primeCompl A h𝔭 hdisj
  have hht : 𝔓.height = 𝔭.height := by
    rw [← IsLocalization.height_under 𝔪.primeCompl 𝔓, hcomap]
  -- `ht 𝔭` is finite
  have hfin : 𝔓.height ≠ ⊤ := by
    rw [hht]
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top h𝔭.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at h1
    have h2 : 𝔭.height ≤ (Nat.card σ : ℕ∞) := by exact_mod_cast h1
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) h2
  -- a maximal regular list in `𝔓`
  obtain ⟨ps, hps, hpsmem, hmax⟩ := exists_maximal_isWeaklyRegular 𝔓 hfin
  have hps𝔪 : ∀ p ∈ ps, p ∈ maximalIdeal A := fun p hp => le_maximalIdeal h𝔓.ne_top (hpsmem p hp)
  -- `𝔓` lies in an associated prime `𝔮` of `A ⧸ (ps)`
  let M := A ⧸ (Ideal.ofList ps • (⊤ : Submodule A A))
  have hsub : (𝔓 : Set A) ⊆ ⋃ q ∈ associatedPrimes A M, q := by
    rw [biUnion_associatedPrimes_eq_compl_regular A M]
    exact fun x hx => hmax x hx
  obtain ⟨𝔮, h𝔮, h𝔓𝔮⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite A M) (f := id) 0 0
    (fun _ h _ _ => h.1)).1 hsub
  -- C1.2's DQ and DL
  have hntM : Nontrivial A := inferInstance
  obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
    exists_isRegular_quotient_ofList (A := A) A ps hps hps𝔪 _ hz' hzm'
  have hDL := length_le_ringKrullDim_quotient_of_mem_associatedPrimes ts htsreg.toIsWeaklyRegular htsmem 𝔮 h𝔮
  -- dimensions
  have hdim1 : ringKrullDim (A ⧸ 𝔮) ≤ ringKrullDim (A ⧸ 𝔓) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor h𝔓𝔮) (Ideal.Quotient.factor_surjective h𝔓𝔮)
  have hdim2 : ringKrullDim (A ⧸ 𝔓) ≤ ringKrullDim (MvPolynomial σ K ⧸ 𝔭) := by
    have := ringKrullDim_quotient_le_of_isLocalization 𝔪.primeCompl 𝔓
    rwa [← Ideal.under_def, hcomap] at this
  -- grade ≤ height
  have hgrade := length_le_height_of_isWeaklyRegular 𝔓 ps hps hpsmem
  rw [hht] at hgrade
  -- assemble
  rw [List.length_map, hzlen] at htslen
  have hts : (ts.length : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := hDL.trans (hdim1.trans (hdim2.trans he))
  have hts' : ts.length ≤ e := by exact_mod_cast hts
  calc (Nat.card σ : ℕ∞) ≤ ((ts.length + ps.length : ℕ) : ℕ∞) := by exact_mod_cast htslen
    _ = (ps.length : ℕ∞) + ts.length := by push_cast; ring
    _ ≤ 𝔭.height + e := add_le_add hgrade (by exact_mod_cast hts')
