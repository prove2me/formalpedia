-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCoarseModuliT.exists_iso_comp_eq_of_isCoarseModuliT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9fa49fb3-040b-5fe1-9bb4-f36db90d4c8e

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT.CerednikDrinfeld.QM NeronModelInfra"
open scoped Quaternion

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.IsCoarseModuliT"
namespace QM
p2m_export "CerednikDrinfeld.QM" "IsCoarseModuliT FakeEllipticCurve.WithExtraLevel FakeEllipticCurve"
namespace IsCoarseModuliT
p2m_export "CerednikDrinfeld.QM.IsCoarseModuliT" "univ ptT_iso ptT_pullback"
namespace UniqT
p2m_open "CerednikDrinfeld.QM.IsCoarseModuliT CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {B : Type} [CommRing B]

theorem exists_hom
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX')
    (hX' : IsCoarseModuliT Λ N ℓ X' πX' pt') :
    ∃! g : X ⟶ X', g ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt' S s u).1 = (pt S s u).1 ≫ g :=
  hX.univ X' πX' pt' hX'.ptT_iso hX'.ptT_pullback

theorem eq_id
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt)
    (h : X ⟶ X) (hh : h ≫ πX = πX)
    (hpt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt S s u).1 = (pt S s u).1 ≫ h) :
    h = 𝟙 X := by
  have hu := hX.univ X πX pt hX.ptT_iso hX.ptT_pullback
  have h1 : (𝟙 X) ≫ πX = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt S s u).1 = (pt S s u).1 ≫ 𝟙 X := by
    refine ⟨Category.id_comp _, ?_⟩
    intro S _ s u
    simp
  exact hu.unique ⟨hh, hpt⟩ h1

end CerednikDrinfeld.QM.IsCoarseModuliT.UniqT

open CerednikDrinfeld.QM.IsCoarseModuliT.UniqT in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX')
    (hX' : IsCoarseModuliT Λ N ℓ X' πX' pt') :
    ∃ i : X ≅ X', i.hom ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt' S s E).1 = (pt S s E).1 ≫ i.hom := by
  obtain ⟨g, ⟨hgπ, hgpt⟩, -⟩ := exists_hom Λ N ℓ X πX pt hX X' πX' pt' hX'
  obtain ⟨g', ⟨hg'π, hg'pt⟩, -⟩ := exists_hom Λ N ℓ X' πX' pt' hX' X πX pt hX
  have hgg' : g ≫ g' = 𝟙 X := by
    refine eq_id Λ N ℓ X πX pt hX (g ≫ g') ?_ ?_
    · rw [Category.assoc, hg'π, hgπ]
    · intro S _ s u
      rw [← Category.assoc, ← hgpt S s u, ← hg'pt S s u]
  have hg'g : g' ≫ g = 𝟙 X' := by
    refine eq_id Λ N ℓ X' πX' pt' hX' (g' ≫ g) ?_ ?_
    · rw [Category.assoc, hgπ, hg'π]
    · intro S _ s u
      rw [← Category.assoc, ← hg'pt S s u, ← hgpt S s u]
  exact ⟨⟨g, g', hgg', hg'g⟩, hgπ, fun S _ s E => hgpt S s E⟩

end S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT (solution)
