-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_isLevelIsogeny_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/791dfa10-f290-5927-9dcb-5aa3ac084bd2

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d D : FakeEllipticCurve Λ N S)
    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ u d) (h : FakeEllipticCurve.Iso d D) :
    FakeEllipticCurve.IsLevelIsogeny ℓ u D := by
  obtain ⟨e, he, hmul_e, hact_e, hlev_e⟩ := h
  obtain ⟨φ, hφ, ψ, hψ, hmulφ, hmulψ, hactφ, hactψ, hℓ, hker, hlev⟩ := hd
  have he' : e.inv ≫ d.f = D.f := by rw [Iso.inv_comp_eq, he]
  have hφ' : (φ ≫ e.hom) ≫ D.f = u.1.f := by rw [Category.assoc, he, hφ]
  have hψ' : (e.inv ≫ ψ) ≫ u.1.f = D.f := by rw [Category.assoc, hψ, he']
  have hmap : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt (φ ≫ e.hom) hφ' P = mapPt e.hom he (mapPt φ hφ P) :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  have hmap' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f),
      mapPt (e.inv ≫ ψ) hψ' P = mapPt ψ hψ (mapPt e.inv he' P) :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  have hinvhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f),
      mapPt e.hom he (mapPt e.inv he' P) = P :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hhominv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t d.f),
      mapPt e.inv he' (mapPt e.hom he P) = P :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id])

  have hmul_einv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f),
      mapPt e.inv he' (D.L.mul t P Q) = d.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
    intro T t P Q
    have h := hmul_e t (mapPt e.inv he' P) (mapPt e.inv he' Q)
    rw [hinvhom, hinvhom] at h
    rw [← h, hhominv]

  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.hom he (d.L.one t) = D.L.one t := by
    intro T t
    letI := D.L.pointGroup t
    have h := hmul_e t (d.L.one t) (d.L.one t)
    rw [d.L.one_mul] at h
    have : mapPt e.hom he (d.L.one t) * 1 = mapPt e.hom he (d.L.one t) * mapPt e.hom he (d.L.one t) := by
      rw [mul_one]; exact h
    exact (mul_left_cancel this).symm
  refine ⟨φ ≫ e.hom, hφ', e.inv ≫ ψ, hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [hmap, hmap, hmap, hmulφ, hmul_e]
  · intro T t P Q
    rw [hmap', hmap', hmap', hmul_einv, hmulψ]
  · intro x
    rw [← Category.assoc, hactφ, Category.assoc, hact_e, Category.assoc]
  · intro x
    have hx : D.act x ≫ e.inv = e.inv ≫ d.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hact_e]
    rw [← Category.assoc, hx, Category.assoc, hactψ, Category.assoc]
  · intro hℓΛ
    obtain ⟨h1, h2⟩ := hℓ hℓΛ
    constructor
    · rw [Category.assoc, ← Category.assoc e.hom, Iso.hom_inv_id, Category.id_comp, h1]
    · rw [Category.assoc, ← Category.assoc ψ, h2, hact_e, Iso.inv_hom_id_assoc]
  · intro T t P
    rw [hmap, ← hker]
    constructor
    · intro h
      have := congrArg (mapPt e.inv he') h
      rw [hhominv] at this
      rw [this, ← hone t, hhominv]
    · intro h
      rw [h, hone]
  · intro T t P hP
    rw [hmap]
    exact (hlev_e t _).1 (hlev t P hP)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso (solution)
