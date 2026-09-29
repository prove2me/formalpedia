-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_hom_comp_eq_specMap_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/90819436-6743-5606-b805-f45d693eebc8

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace GalCoarseT

theorem spec_comp_symm {K : Type} [CommRing K] (τ : K ≃+* K) :
    Spec.map (CommRingCat.ofHom (τ : K →+* K)) ≫ Spec.map (CommRingCat.ofHom (τ.symm : K →+* K)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom (τ.toRingHom.comp τ.symm.toRingHom)) = 𝟙 _
  rw [RingEquiv.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem spec_symm_comp {K : Type} [CommRing K] (τ : K ≃+* K) :
    Spec.map (CommRingCat.ofHom (τ.symm : K →+* K)) ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)) = 𝟙 _ := by
  have := spec_comp_symm τ.symm
  simpa using this

end GalCoarseT

open GalCoarseT in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {K : Type} [CommRing K]
    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of K))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (hco : IsCoarseModuliT Λ N ℓ 𝒴 g ptT) (τ : K ≃+* K) :
    ∃! h : 𝒴 ⟶ 𝒴, h ≫ g = g ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)) ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT S (s ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) u).1 = (ptT S s u).1 ≫ h := by
  classical
  set sτ := Spec.map (CommRingCat.ofHom (τ : K →+* K)) with hsτ
  set sτ' := Spec.map (CommRingCat.ofHom (τ.symm : K →+* K)) with hsτ'
  have h1 : sτ ≫ sτ' = 𝟙 _ := spec_comp_symm τ
  have h2 : sτ' ≫ sτ = 𝟙 _ := spec_symm_comp τ

  let pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s (g ≫ sτ') :=
    fun S _ s u => ⟨(ptT S (s ≫ sτ) u).1, by
      rw [← Category.assoc, (ptT S (s ≫ sτ) u).2, Category.assoc, h1, Category.comp_id]⟩
  have hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u' := by
    intro S _ s u u' huu'
    apply Subtype.ext
    show (ptT S (s ≫ sτ) u).1 = (ptT S (s ≫ sτ) u').1
    rw [hco.ptT_iso S (s ≫ sτ) u u' huu']
  have hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of K)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of K)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1 := by
    intro S S' _ _ φ s s' hs u u' hpu
    show (ptT S' (s' ≫ sτ) u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S (s ≫ sτ) u).1
    exact hco.ptT_pullback S S' φ (s ≫ sτ) (s' ≫ sτ) (by rw [← Category.assoc, hs]) u u' hpu
  obtain ⟨h, ⟨hhg, hhpt⟩, huniq⟩ := hco.univ 𝒴 (g ≫ sτ') pt' hiso hpb
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  ·
    have := congrArg (· ≫ sτ) hhg
    simp only [Category.assoc, h2, Category.comp_id] at this
    exact this
  · intro S _ s u
    exact hhpt S s u
  ·
    intro h' ⟨hh'g, hh'pt⟩
    apply huniq
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, hh'g, Category.assoc, h1, Category.comp_id]
    · intro S _ s u
      exact hh'pt S s u

end S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv (solution)
