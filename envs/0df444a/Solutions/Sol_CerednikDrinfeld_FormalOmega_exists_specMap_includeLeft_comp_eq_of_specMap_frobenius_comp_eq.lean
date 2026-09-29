-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8a58ec33-dd68-57bb-9c7a-8445e2ff0239

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels
import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_opens_preimage_eq_of_isCompact_of_preimage_frobenius_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_specMap_includeLeft_comp_eq_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ExDesc

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

section Period
variable {R : Type} [CommRing R] (τ : R →+* R) (k : ℕ) (f : R)

theorem iterate_mul_eq (hf : τ^[k] f = f) (q : ℕ) : τ^[k * q] f = f := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hf, ih]

theorem mem_iterate_comap_asIdeal (n : ℕ) (x : PrimeSpectrum R) (a : R) :
    a ∈ ((PrimeSpectrum.comap τ)^[n] x).asIdeal ↔ τ^[n] a ∈ x.asIdeal := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ih]

end Period

end ExDesc

namespace ExDesc

theorem exists_ringHom_comp_eq
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
    (B' : Type) [CommRing B'] [Algebra 𝒪 B'] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B'] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B']
    (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    {R₀ : Type} [CommRing R₀] (φ₀ : R₀ →+* B' ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
    (hφ₀ : ∀ a, Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B') (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (φ₀ a) = φ₀ a) :
    ∃ ψ : R₀ →+* B', (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr).comp ψ = φ₀ := by
  classical
  have haff := CerednikDrinfeld.FormalOmega.existsUnique_tmul_one_eq_of_map_frobenius_eq 𝒪 hdvr π hπ hcomplete hres hunr
    Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B' hB'
  have hinj := includeLeft_injective 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr
    m hm FrS hFrS B' hB'
  choose ψf hψf _huniq using fun a => haff (φ₀ a) (hφ₀ a)
  have hψι : ∀ a, (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (ψf a) = φ₀ a :=
    fun a => (hψf a).symm
  have h1 : ψf 1 = 1 := by
    apply hinj
    rw [hψι, φ₀.map_one, RingHom.map_one]
  have h0 : ψf 0 = 0 := by
    apply hinj
    rw [hψι, φ₀.map_zero, RingHom.map_zero]
  have hmul : ∀ a a', ψf (a * a') = ψf a * ψf a' := by
    intro a a'
    apply hinj
    rw [hψι, φ₀.map_mul, RingHom.map_mul, hψι, hψι]
  have hadd : ∀ a a', ψf (a + a') = ψf a + ψf a' := by
    intro a a'
    apply hinj
    rw [hψι, φ₀.map_add, RingHom.map_add, hψι, hψι]
  exact ⟨{ toFun := ψf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }, RingHom.ext fun a => hψι a⟩

theorem exists_chart
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
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (hf : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ≫ f = f)
    (b : B) (W : T.Opens) (hW : IsAffineOpen W)
    (hbW : ∀ z : ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) z ∈ PrimeSpectrum.basicOpen b →
        f z ∈ W) :
    ∃ g : Spec (CommRingCat.of (Localization.Away b)) ⟶ T,
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away b →+* Localization.Away b ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ g =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B (Localization.Away b)) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom) ≫ f := by
  classical
  let Bb := Localization.Away b
  let jb : B →+* Bb := algebraMap B Bb
  let ι : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := Algebra.TensorProduct.includeLeftRingHom
  let ιb : Bb →+* Bb ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := Algebra.TensorProduct.includeLeftRingHom
  let σA := Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
  let σb := Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Bb) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
  let mapjA := Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bb) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)
  let mapj : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →+* Bb ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := mapjA.toRingHom
  have hsq : ιb.comp jb = mapj.comp ι := by
    ext x
    simp [ιb, jb, mapj, mapjA, ι, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hστ : σb.toRingHom.comp mapj = mapj.comp σA.toRingHom := by
    have : σb.comp mapjA = mapjA.comp σA := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp [σb, mapjA, σA]
    exact congrArg AlgHom.toRingHom this

  have hrange : Set.range ⇑(Spec.map (CommRingCat.ofHom mapj) ≫ f).base ⊆ Set.range ⇑(Scheme.Opens.ι W).base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (Spec.map (CommRingCat.ofHom mapj) ≫ f) z ∈ W
    rw [Scheme.Hom.comp_apply]
    apply hbW
    rw [Spec.map_apply, CommRingCat.hom_ofHom]
    show PrimeSpectrum.comap ι (PrimeSpectrum.comap mapj z) ∈ PrimeSpectrum.basicOpen b
    rw [← PrimeSpectrum.comap_comp_apply, ← hsq, PrimeSpectrum.comap_comp_apply,
      ← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range Bb b]
    exact ⟨_, rfl⟩
  let k := IsOpenImmersion.lift (Scheme.Opens.ι W) (Spec.map (CommRingCat.ofHom mapj) ≫ f) hrange
  have hk : k ≫ Scheme.Opens.ι W = Spec.map (CommRingCat.ofHom mapj) ≫ f := IsOpenImmersion.lift_fac _ _ _
  haveI : IsAffine (W : Scheme) := hW
  let eW := Scheme.isoSpec (W : Scheme)
  let φ := Spec.preimage (k ≫ eW.hom)
  have hφ : Spec.map φ = k ≫ eW.hom := Spec.map_preimage _

  have hinvk : Spec.map (CommRingCat.ofHom σb.toRingHom) ≫ k = k := by
    rw [← cancel_mono (Scheme.Opens.ι W), Category.assoc, hk, ← Category.assoc, fold, hστ, ← fold, Category.assoc, hf]
  have hinvφ : ∀ a, σb (φ.hom a) = φ.hom a := by
    have e1 : Spec.map (φ ≫ CommRingCat.ofHom σb.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hinvk]
    have e2 := Spec.map_injective e1
    intro a
    have := congrArg (fun ψ : _ ⟶ CommRingCat.of (Bb ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) => ψ.hom a) e2
    simpa using this

  have hBb : IsNilpotent (algebraMap 𝒪 Bb π) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [IsScalarTower.algebraMap_apply 𝒪 B Bb, ← map_pow, hn, map_zero]⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_comp_eq 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    hFr m hm FrS hFrS Bb hBb φ.hom hinvφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ eW.inv ≫ Scheme.Opens.ι W, ?_⟩
  rw [← Category.assoc, fold, hψ, CommRingCat.ofHom_hom, hφ, Category.assoc, eW.hom_inv_id_assoc, hk]

end ExDesc

namespace ExDesc

theorem exists_period
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
    (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    ∀ z : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr, ∃ k, 0 < k ∧
      (⇑(Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom)^[k] z = z := by
  classical
  let σA := Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
  let τ : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := σA.toRingHom
  have hτ : ∀ z, τ z = σA z := fun _ => rfl
  obtain ⟨N, hN⟩ := hB
  obtain ⟨hlev, -⟩ := CerednikDrinfeld.FormalOmega.fixedPoints_frobenius_levels 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr
    hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS
  have htmul : ∀ (n : ℕ) (b : B) (x : Onr), τ^[n] (b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x) = b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] ((FrS ^ n) x) := by
    intro n b x
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply, hτ]
        exact Algebra.TensorProduct.map_tmul _ _ _ _
  intro z
  show ∃ k, 0 < k ∧ τ^[k] z = z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by simp⟩
  | tmul b x =>
      obtain ⟨k, hk, x', hx', hd⟩ := hlev N x
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hd
      have hx : x = x' + y * (algebraMap 𝒪 Onr π) ^ N := by rw [hy]; ring
      have hkill : b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (y * (algebraMap 𝒪 Onr π) ^ N) = 0 := by
        have h1 : y * (algebraMap 𝒪 Onr π) ^ N = (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) (π ^ N)) • y := by
          rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr, map_pow, mul_comm]
        have h2 : (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) (π ^ N)) • b = 0 := by
          rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B, map_pow, hN, zero_mul]
        rw [h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]
      have hbx : b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x = b ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] x' := by rw [hx, TensorProduct.tmul_add, hkill, add_zero]
      have hfix : (FrS ^ k) x' = x' := by
        have := (AlgHom.mem_equalizer _ _ _).mp hx'
        simpa using this
      refine ⟨k, hk, ?_⟩
      rw [hbx, htmul, hfix]
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨k₁, hk₁, e₁⟩ := h₁
      obtain ⟨k₂, hk₂, e₂⟩ := h₂
      refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
      rw [← RingHom.coe_pow, map_add, RingHom.coe_pow, iterate_mul_eq τ k₁ z₁ e₁ k₂, mul_comm,
        iterate_mul_eq τ k₂ z₂ e₂ k₁]

theorem exists_goodChart
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
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (hf : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ≫ f = f) (x : ↥(Spec (CommRingCat.of B))) :
    ∃ (b : B) (W : T.Opens), IsAffineOpen W ∧ x ∈ PrimeSpectrum.basicOpen b ∧
      ∀ z : ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))),
        PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) z ∈ PrimeSpectrum.basicOpen b →
          f z ∈ W := by
  classical
  let σA := Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)
  let τ : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := σA.toRingHom
  let ι : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr := Algebra.TensorProduct.includeLeftRingHom
  have hper := exists_period 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm
    FrS hFrS B hB

  let gσ : PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) → PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) := PrimeSpectrum.comap τ
  have hfσ : ∀ z : ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))), f (gσ z) = f z := by
    intro z
    have := congrArg (fun k : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T => k z) hf
    simp only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hfσn : ∀ (n : ℕ) (z : ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)))), f (gσ^[n] z) = f z := by
    intro n; induction n with
    | zero => intro z; rfl
    | succ n ih => intro z; rw [Function.iterate_succ_apply', hfσ, ih]
  have hsurj := comap_includeLeft_surjective 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg
    hOnr_closed hFr m hm FrS hFrS B hB
  obtain ⟨y, hy⟩ := hsurj x
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ

  have hyU : y ∈ f ⁻¹ᵁ W := hyW
  obtain ⟨_, ⟨h, rfl⟩, hyh, hhW⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).exists_subset_of_mem_open hyU (f ⁻¹ᵁ W).isOpen
  obtain ⟨K, hK, hKh⟩ := hper h

  let U' : (Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))).Opens := ⨆ j : Fin K, PrimeSpectrum.basicOpen (τ^[(j : ℕ)] h)
  have hmemU' : ∀ z : PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr), z ∈ U' ↔ ∃ j : Fin K, τ^[(j : ℕ)] h ∉ z.asIdeal := by
    intro z
    change z ∈ (⨆ j : Fin K, PrimeSpectrum.basicOpen (τ^[(j : ℕ)] h) : TopologicalSpace.Opens (PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))) ↔ _
    rw [TopologicalSpace.Opens.mem_iSup]
    simp only [PrimeSpectrum.mem_basicOpen]
  have hU'c : IsCompact (U' : Set ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)))) := by
    have : IsCompact ((⨆ j : Fin K, PrimeSpectrum.basicOpen (τ^[(j : ℕ)] h) :
        TopologicalSpace.Opens (PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))) : Set (PrimeSpectrum (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))) := by
      simp only [TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun j => PrimeSpectrum.isCompact_basicOpen _
    exact this
  have hU'σ : Spec.map (CommRingCat.ofHom τ) ⁻¹ᵁ U' = U' := by
    ext z
    rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Spec.map_apply, CommRingCat.hom_ofHom]
    refine (hmemU' (PrimeSpectrum.comap τ z)).trans (Iff.trans ?_ (hmemU' z).symm)
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hstep : ∀ n : ℕ, τ (τ^[n] h) = τ^[n + 1] h := fun n => (Function.iterate_succ_apply' τ n h).symm
    constructor
    · rintro ⟨j, hj⟩
      rw [hstep] at hj
      by_cases hjK : (j : ℕ) + 1 < K
      · exact ⟨⟨(j : ℕ) + 1, hjK⟩, hj⟩
      · have hjK' : (j : ℕ) + 1 = K := by omega
        refine ⟨⟨0, hK⟩, ?_⟩
        rw [hjK', hKh] at hj
        exact hj
    · rintro ⟨j, hj⟩
      by_cases hj0 : (j : ℕ) = 0
      · refine ⟨⟨K - 1, by omega⟩, ?_⟩
        rw [hstep, show (K - 1 : ℕ) + 1 = K by omega, hKh]
        rw [hj0] at hj
        exact hj
      · refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_⟩
        rw [hstep, show ((j : ℕ) - 1) + 1 = (j : ℕ) by omega]
        exact hj
  obtain ⟨V, -, hV⟩ := CerednikDrinfeld.FormalOmega.exists_opens_preimage_eq_of_isCompact_of_preimage_frobenius_eq 𝒪 hdvr π hπ
    hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B hB U' hU'c hU'σ

  have hpre : ∀ z : ↥(Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))), PrimeSpectrum.comap ι z ∈ V ↔ z ∈ U' := by
    intro z
    rw [← hV, Scheme.Hom.mem_preimage, Spec.map_apply, CommRingCat.hom_ofHom]
    exact Iff.rfl
  have hxV : x ∈ V := by
    rw [← hy]
    exact (hpre y).mpr ((hmemU' y).mpr ⟨⟨0, hK⟩, hyh⟩)
  obtain ⟨_, ⟨b, rfl⟩, hxb, hbV⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hxV V.isOpen
  refine ⟨b, W, hW, hxb, fun z hz => ?_⟩
  have hzU : z ∈ U' := (hpre z).mp (hbV hz)
  obtain ⟨j, hj⟩ := (hmemU' z).mp hzU
  rw [← mem_iterate_comap_asIdeal τ] at hj
  have : f (gσ^[(j : ℕ)] z) ∈ W := hhW hj
  rw [hfσn] at this
  exact this

end ExDesc

namespace ExDesc

theorem restrict_key
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
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (Bc C : Type) [CommRing Bc] [Algebra B Bc] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Bc] [IsScalarTower ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bc]
    [CommRing C] [Algebra B C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B C]
    (i : Bc →+* C) (hi : ∀ x : B, i (algebraMap B Bc x) = algebraMap B C x)
    (gc : Spec (CommRingCat.of Bc) ⟶ T)
    (hgc : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Bc →+* Bc ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ gc =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bc)
        (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom) ≫ f) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫
        (Spec.map (CommRingCat.ofHom i) ≫ gc) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B C)
        (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom) ≫ f := by
  let i' : Bc →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] C :=
    { toRingHom := i
      commutes' := fun s => by
        rw [IsScalarTower.algebraMap_apply ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bc, IsScalarTower.algebraMap_apply ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B C]
        exact hi _ }
  have h1 : (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr).comp i =
      (Algebra.TensorProduct.map i' (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : Bc →+* Bc ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) := by
    ext x
    simp [Algebra.TensorProduct.includeLeftRingHom_apply, i']
  have h2 : (Algebra.TensorProduct.map i' (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bc) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B C) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom := by
    have : (Algebra.TensorProduct.map i' (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B Bc) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B C) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr) := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp [i', hi]
    exact congrArg AlgHom.toRingHom this
  rw [← Category.assoc, fold, h1, ← fold, Category.assoc, hgc, ← Category.assoc, fold, h2]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem pullback_key
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
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (b : B) (gc : Spec (CommRingCat.of (Localization.Away b)) ⟶ T)
    (hgc : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away b →+* Localization.Away b ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ gc =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B (Localization.Away b))
        (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)).toRingHom) ≫ f) :
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))) ≫ gc =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))) ≫ f := by
  rw [← cancel_epi (pullbackSpecIso B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (Localization.Away b)).inv, pullbackSpecIso_inv_snd_assoc,
    pullbackSpecIso_inv_fst_assoc]

  obtain ⟨θ, hθ⟩ : ∃ θ : (Localization.Away b) ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr →+* ((B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) ⊗[B] Localization.Away b),
      ∀ (a : Localization.Away b) (o : Onr), θ (a ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] o) = ((1 : B) ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] o) ⊗ₜ[B] a := by
    refine ⟨(Algebra.TensorProduct.comm B (Localization.Away b) (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom.comp
      (Algebra.TensorProduct.cancelBaseChange ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B B (Localization.Away b) Onr).symm.toRingHom, fun a o => ?_⟩
    simp [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.comm_tmul]
  have hθ1 : θ.comp (Algebra.TensorProduct.includeLeftRingHom : Localization.Away b →+* Localization.Away b ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) =
      RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
        Localization.Away b →ₐ[B] (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) ⊗[B] Localization.Away b) := by
    ext a
    rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, hθ, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, ← Algebra.TensorProduct.one_def]
  have key : ∀ z : B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr,
      θ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B (Localization.Away b)) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr) z) =
        Algebra.TensorProduct.includeLeftRingHom z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x o =>
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom', hθ,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  rw [show RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Localization.Away b →ₐ[B] ((B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) ⊗[B] Localization.Away b)) =
      θ.comp (Algebra.TensorProduct.includeLeftRingHom : Localization.Away b →+* Localization.Away b ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) from hθ1.symm,
    ← fold, Category.assoc, hgc, ← Category.assoc, fold]
  congr 2
  congr 1
  refine RingHom.ext fun z => ?_
  rw [RingHom.comp_apply]
  exact key z

end ExDesc

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
open ExDesc in
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
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (hf : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ≫ f = f) :
    ∃ g : Spec (CommRingCat.of B) ⟶ T,
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ g = f := by
  classical

  have hch := fun x => exists_goodChart 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m
    hm FrS hFrS B hB T f hf x
  choose bx Wx hWx hbx hbW using hch
  have hg := fun x => exists_chart 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm
    FrS hFrS B hB T f hf (bx x) (Wx x) (hWx x) (hbW x)
  choose gch hgch using hg

  let 𝒱 : (Spec (CommRingCat.of B)).OpenCover :=
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

  have hcompat : ∀ x x' : ↥(Spec (CommRingCat.of B)),
      pullback.fst (𝒱.f x) (𝒱.f x') ≫ gch x = pullback.snd (𝒱.f x) (𝒱.f x') ≫ gch x' := by
    intro x x'
    show pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x)))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x'))))) ≫ gch x =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x)))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x'))))) ≫ gch x'
    rw [← cancel_epi (pullbackSpecIso B (Localization.Away (bx x)) (Localization.Away (bx x'))).inv,
      pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
    have hC : IsNilpotent (algebraMap 𝒪 (Localization.Away (bx x) ⊗[B] Localization.Away (bx x')) π) := by
      obtain ⟨N, hN⟩ := hB
      refine ⟨N, ?_⟩
      rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (bx x) ⊗[B] Localization.Away (bx x')), ← map_pow, hN, map_zero]
    apply CerednikDrinfeld.FormalOmega.eq_of_specMap_includeLeft_comp_eq_of_isNilpotent 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr
      hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS (Localization.Away (bx x) ⊗[B] Localization.Away (bx x')) hC T
    rw [restrict_key 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B hB T f
        (Localization.Away (bx x)) (Localization.Away (bx x) ⊗[B] Localization.Away (bx x')) _ (fun y => rfl) (gch x) (hgch x),
      restrict_key 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B hB T f
        (Localization.Away (bx x')) (Localization.Away (bx x) ⊗[B] Localization.Away (bx x'))
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          Localization.Away (bx x') →ₐ[B] Localization.Away (bx x) ⊗[B] Localization.Away (bx x')))
        (fun y => (Algebra.TensorProduct.includeRight :
          Localization.Away (bx x') →ₐ[B] Localization.Away (bx x) ⊗[B] Localization.Away (bx x')).commutes y)
        (gch x') (hgch x')]
  refine ⟨𝒱.glueMorphisms gch hcompat, ?_⟩

  have e : (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) = algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) :=
    RingHom.ext fun y => rfl
  rw [e]
  refine Scheme.Cover.hom_ext (𝒱.pullback₁ (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))))) _ _ fun x => ?_
  show pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x))))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))) ≫ 𝒱.glueMorphisms gch hcompat =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x))))) ≫ f
  rw [← Category.assoc, pullback.condition, Category.assoc]
  have hι : 𝒱.f x ≫ 𝒱.glueMorphisms gch hcompat = gch x := Scheme.Cover.ι_glueMorphisms 𝒱 gch hcompat x
  rw [show Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (bx x)))) ≫ 𝒱.glueMorphisms gch hcompat = gch x from hι]
  exact pullback_key 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm FrS hFrS B hB T f
    (bx x) (gch x) (hgch x)

end S_CerednikDrinfeld_FormalOmega_exists_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq (solution)
