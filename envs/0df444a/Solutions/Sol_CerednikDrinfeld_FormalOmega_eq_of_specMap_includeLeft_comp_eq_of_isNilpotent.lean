-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.eq_of_specMap_includeLeft_comp_eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/511d9bce-11df-555d-b70b-3e2bb6c3c32c

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_specMap_includeLeft_comp_eq_of_isNilpotent

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

namespace EpiDesc

section Frame

variable {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)

include hdvr hπ hcomplete hres hunr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hm hFrS in

theorem includeLeft_injective (B' : Type) [CommRing B'] [Algebra 𝒪 B'] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B'] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B']
    (hB' : IsNilpotent (algebraMap 𝒪 B' π)) :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) := by
  have haff := CerednikDrinfeld.FormalOmega.existsUnique_tmul_one_eq_of_map_frobenius_eq 𝒪 hdvr π hπ hcomplete hres hunr
    Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B' hB'
  intro b₁ b₂ h
  have hfix : Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B') (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (b₁ ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr)) =
      b₁ ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr) := by
    rw [Algebra.TensorProduct.map_tmul]
    simp
  obtain ⟨b, hb, huniq⟩ := haff _ hfix
  have e₁ : b₁ = b := huniq b₁ rfl
  have e₂ : b₂ = b := huniq b₂ (by
    show b₁ ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr) = b₂ ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (1 : Onr)
    exact h)
  rw [e₁, e₂]

include hdvr hπ hcomplete hres hunr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hm hFrS in

theorem comap_includeLeft_surjective (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    Function.Surjective (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) := by
  classical
  intro q

  let K := q.asIdeal.ResidueField
  haveI : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) K := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply 𝒪 B K, IsScalarTower.algebraMap_apply ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B K,
      IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B])
  have hK : IsNilpotent (algebraMap 𝒪 K π) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [IsScalarTower.algebraMap_apply 𝒪 B K, ← map_pow, hn, map_zero]⟩
  have hinj := includeLeft_injective 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr
    m hm FrS hFrS K hK

  haveI : Nontrivial (K ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) := hinj.nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
  let ψ : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] K ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B K) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)
  refine ⟨⟨M.comap ψ.toRingHom, Ideal.comap_isPrime _ _⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal]
  show (M.comap ψ.toRingHom).comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) = q.asIdeal
  have hnat : ψ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) =
      (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr).comp (algebraMap B K) := by
    ext b
    simp [ψ, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [Ideal.comap_comap, hnat, ← Ideal.comap_comap]
  have hbot : M.comap (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) = ⊥ := by
    rcases Ideal.eq_bot_or_top (M.comap (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) with h | h
    · exact h
    · exact absurd (Ideal.comap_eq_top_iff.mp h) hM.ne_top
  rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end Frame

section Generic

theorem specMap_ofHom_preimage {R S : Type} [CommRing R] [CommRing S]
    (w : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (Spec.preimage w).hom) = w := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem fold {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : S →+* T) (b : R →+* S) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (a b : R →+* S)
    (h : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b)) : a = b := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

end Generic

end EpiDesc

open EpiDesc in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B]
    (hB : IsNilpotent (algebraMap 𝒪 B π))
    (T : Scheme.{0}) (g₁ g₂ : Spec (CommRingCat.of B) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ g₁ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ g₂) :
    g₁ = g₂ := by
  classical
  let ι : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := Algebra.TensorProduct.includeLeftRingHom

  have hpt : ∀ x : ↥(Spec (CommRingCat.of B)), g₁ x = g₂ x := by
    intro x
    obtain ⟨y, hy⟩ := comap_includeLeft_surjective 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg
      hOnr_closed hFr m hm FrS hFrS B hB x
    have this : (Spec.map (CommRingCat.ofHom ι) ≫ g₁) y = (Spec.map (CommRingCat.ofHom ι) ≫ g₂) y := by rw [h]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom] at this
    rw [← hy]
    exact this

  have hdata : ∀ x : ↥(Spec (CommRingCat.of B)), ∃ b : B, x ∈ PrimeSpectrum.basicOpen b ∧
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫ g₁ =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b))) ≫ g₂ := by
    intro x

    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g₁ x)) isOpen_univ
    have hxO : x ∈ (g₁ ⁻¹ᵁ W ⊓ g₂ ⁻¹ᵁ W : (Spec (CommRingCat.of B)).Opens) := ⟨hxW, by
      show g₂ x ∈ W; rw [← hpt]; exact hxW⟩
    obtain ⟨_, ⟨b, rfl⟩, hxb, hbO⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hxO
      (g₁ ⁻¹ᵁ W ⊓ g₂ ⁻¹ᵁ W).isOpen
    refine ⟨b, hxb, ?_⟩

    let Bb := Localization.Away b
    let jb : B →+* Bb := algebraMap B Bb
    have hq : ∀ y, Spec.map (CommRingCat.ofHom jb) y ∈ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
      intro y
      rw [← PrimeSpectrum.localization_away_comap_range Bb b]
      refine ⟨y, ?_⟩
      show PrimeSpectrum.comap (algebraMap B Bb) y = Spec.map (CommRingCat.ofHom jb) y
      rw [Spec.map_apply, CommRingCat.hom_ofHom]

    have hrange : ∀ g : Spec (CommRingCat.of B) ⟶ T, PrimeSpectrum.basicOpen b ≤ g ⁻¹ᵁ W →
        Set.range ⇑(Spec.map (CommRingCat.ofHom jb) ≫ g).base ⊆ Set.range ⇑(Scheme.Opens.ι W).base := by
      intro g hg
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (Spec.map (CommRingCat.ofHom jb) ≫ g) y ∈ W
      rw [Scheme.Hom.comp_apply]
      exact hg (hq y)
    have h1 : PrimeSpectrum.basicOpen b ≤ g₁ ⁻¹ᵁ W := fun z hz => (hbO hz).1
    have h2 : PrimeSpectrum.basicOpen b ≤ g₂ ⁻¹ᵁ W := fun z hz => (hbO hz).2
    let k₁ := IsOpenImmersion.lift (Scheme.Opens.ι W) (Spec.map (CommRingCat.ofHom jb) ≫ g₁) (hrange g₁ h1)
    let k₂ := IsOpenImmersion.lift (Scheme.Opens.ι W) (Spec.map (CommRingCat.ofHom jb) ≫ g₂) (hrange g₂ h2)
    have hk₁ : k₁ ≫ Scheme.Opens.ι W = Spec.map (CommRingCat.ofHom jb) ≫ g₁ := IsOpenImmersion.lift_fac _ _ _
    have hk₂ : k₂ ≫ Scheme.Opens.ι W = Spec.map (CommRingCat.ofHom jb) ≫ g₂ := IsOpenImmersion.lift_fac _ _ _

    haveI : IsAffine (W : Scheme) := hW
    let eW := Scheme.isoSpec (W : Scheme)
    let ψ₁ := Spec.preimage (k₁ ≫ eW.hom)
    let ψ₂ := Spec.preimage (k₂ ≫ eW.hom)
    have hψ₁ : Spec.map ψ₁ = k₁ ≫ eW.hom := Spec.map_preimage _
    have hψ₂ : Spec.map ψ₂ = k₂ ≫ eW.hom := Spec.map_preimage _

    have hBb : IsNilpotent (algebraMap 𝒪 Bb π) := by
      obtain ⟨n, hn⟩ := hB
      exact ⟨n, by rw [IsScalarTower.algebraMap_apply 𝒪 B Bb, ← map_pow, hn, map_zero]⟩
    have hinj := includeLeft_injective 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr
      m hm FrS hFrS Bb hBb
    let ιb : Bb →+* Bb ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := Algebra.TensorProduct.includeLeftRingHom
    let mapj : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →+* Bb ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bb) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom
    have hsq : ιb.comp jb = mapj.comp ι := by
      ext x
      simp [ιb, jb, mapj, ι, Algebra.TensorProduct.includeLeftRingHom_apply]

    have hkey : Spec.map (CommRingCat.ofHom ιb) ≫ k₁ = Spec.map (CommRingCat.ofHom ιb) ≫ k₂ := by
      rw [← cancel_mono (Scheme.Opens.ι W), Category.assoc, Category.assoc, hk₁, hk₂, ← Category.assoc, ← Category.assoc,
        fold, hsq, ← fold, Category.assoc, Category.assoc, h]
    have hψ : ψ₁ = ψ₂ := by
      have e1 : Spec.map (ψ₁ ≫ CommRingCat.ofHom ιb) = Spec.map (ψ₂ ≫ CommRingCat.ofHom ιb) := by
        rw [Spec.map_comp, Spec.map_comp, hψ₁, hψ₂, ← Category.assoc, ← Category.assoc, hkey]
      have e2 := Spec.map_injective e1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      apply hinj
      have := congrArg (fun φ : _ ⟶ CommRingCat.of (Bb ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) => φ.hom a) e2
      simp at this
      exact this
    have hk : k₁ = k₂ := by
      rw [← cancel_mono eW.hom, ← hψ₁, ← hψ₂, hψ]
    rw [← hk₁, ← hk₂, hk]
  choose bx hbx hloc using hdata
  let 𝒰 : (Spec (CommRingCat.of B)).OpenCover :=
    { I₀ := ↥(Spec (CommRingCat.of B))
      X := fun x => Spec (CommRingCat.of (Localization.Away (bx x)))
      f := fun x => Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x))))
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ⟨x, ?_⟩, fun x => inferInstance⟩
        have : x ∈ (PrimeSpectrum.basicOpen (bx x) : Set (PrimeSpectrum B)) := hbx x
        rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (bx x)) (bx x)] at this
        obtain ⟨y, hy⟩ := this
        refine ⟨y, ?_⟩
        show Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x)))) y = x
        rw [Spec.map_apply, CommRingCat.hom_ofHom]
        exact hy }
  exact Scheme.Cover.hom_ext 𝒰 g₁ g₂ hloc

end S_CerednikDrinfeld_FormalOmega_eq_of_specMap_includeLeft_comp_eq_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_eq_of_specMap_includeLeft_comp_eq_of_isNilpotent (solution)
