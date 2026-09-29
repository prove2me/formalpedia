-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCoarseModuliT.exists_hom_pullback_bijective_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2d7316a1-c0c3-51c7-9c2b-ab8bc9e01af0

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    {B₀ B₁ : Type} [CommRing B₀] [CommRing B₁] (ι : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of B₀))

    (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of B₀))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g)
    (ptT_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u')
    (ptT_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B₀)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1)
    (ptT_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (y : SchemeHomOver s g), ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, ptT k s u = y)
    (ptT_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₀))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ k), ptT k s u = ptT k s u' → FakeEllipticCurve.WithExtraLevel.Iso u u')

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B₁))
    (ptY : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptY) :
    ∃ h : Y ⟶ pullback g ι,
      h ≫ pullback.snd g ι = πY ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptY S s u).1 ≫ h ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1) ∧
      (∀ h' : Y ⟶ pullback g ι, h' ≫ pullback.snd g ι = πY →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
          (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (ptY S s u).1 ≫ h' ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1) →
        h' = h) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (P P' : SchemeHomOver s πY), P.1 ≫ h = P'.1 ≫ h → P = P') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B₁))
        (Q : SchemeHomOver s (pullback.snd g ι)), ∃ P : SchemeHomOver s πY, P.1 ≫ h = Q.1) := by

  let pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s (pullback.snd g ι) :=
    fun S _ s u => ⟨pullback.lift (ptT S (s ≫ ι) u).1 s (by rw [(ptT S (s ≫ ι) u).2]), pullback.lift_snd _ _ _⟩
  have hpt'fst : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), (pt' S s u).1 ≫ pullback.fst g ι = (ptT S (s ≫ ι) u).1 :=
    fun S _ s u => pullback.lift_fst _ _ _

  have hi : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u' := by
    intro S _ s u u' e
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [hpt'fst, hpt'fst, ptT_iso S (s ≫ ι) u u' e]
    · rw [(pt' S s u).2, (pt' S s u').2]

  have hb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₁)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B₁)),
      Spec.map (CommRingCat.ofHom ψ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'), FakeEllipticCurve.WithExtraLevel.IsPullback ψ u u' →
        (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt' S s u).1 := by
    intro S S' _ _ ψ s s' hs u u' hp
    apply pullback.hom_ext
    · rw [Category.assoc, hpt'fst, hpt'fst]
      exact ptT_pullback S S' ψ (s ≫ ι) (s' ≫ ι) (by rw [← Category.assoc, hs]) u u' hp
    · rw [Category.assoc, (pt' S s u).2, (pt' S' s' u').2, hs]

  obtain ⟨h, ⟨hh, hhpt⟩, huniq⟩ := hY.univ (pullback g ι) (pullback.snd g ι) pt' hi hb
  refine ⟨h, hh, ?_, ?_, ?_, ?_⟩
  · intro S _ s u
    rw [← Category.assoc, ← hhpt S s u, hpt'fst]
  · intro h' hh' hh'pt
    refine huniq h' ⟨hh', fun S _ s u => ?_⟩
    apply pullback.hom_ext
    · rw [hpt'fst, Category.assoc, hh'pt S s u]
    · rw [(pt' S s u).2, Category.assoc, hh', (ptY S s u).2]
  ·
    intro k _ _ s P P' hPP'
    obtain ⟨u, hu⟩ := hY.ptT_surjective k s P
    obtain ⟨u', hu'⟩ := hY.ptT_surjective k s P'
    have key : ptT k (s ≫ ι) u = ptT k (s ≫ ι) u' := by
      apply Subtype.ext
      rw [← hpt'fst, ← hpt'fst, hhpt k s u, hhpt k s u', hu, hu', hPP']
    have e : FakeEllipticCurve.WithExtraLevel.Iso u u' := ptT_injective k (s ≫ ι) u u' key
    rw [← hu, ← hu']
    exact hY.ptT_iso k s u u' e
  ·
    intro k _ _ s Q
    obtain ⟨u, hu⟩ := ptT_surjective k (s ≫ ι)
      ⟨Q.1 ≫ pullback.fst g ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩
    refine ⟨ptY k s u, ?_⟩
    apply pullback.hom_ext
    · rw [← hhpt k s u, hpt'fst, hu]
    · rw [Category.assoc, hh, (ptY k s u).2, Q.2]

end S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_hom_pullback_bijective_points (solution)
