-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_iso_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ad88c5b2-db7e-5ac6-b352-fa19d9b3e81a

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace ExtraLevelTransport

variable {R : Type} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem map_one_of_hom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem map_nsmulPt_of_hom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact map_one_of_hom L L' φ hφ hhom t
  | succ n ih => simp only [nsmulPt]; rw [hhom, ih]

theorem map_inv_of_hom {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    mapPt φ hφ (L.inv t P) = L'.inv t (mapPt φ hφ P) := by

  have h1 : L'.mul t (mapPt φ hφ (L.inv t P)) (mapPt φ hφ P) = L'.one t := by
    rw [← hhom, L.inv_mul_cancel, map_one_of_hom L L' φ hφ hhom t]
  have := congrArg (fun Q => L'.mul t Q (L'.inv t (mapPt φ hφ P))) h1
  rw [L'.mul_assoc, L'.mul_inv_cancel, L'.mul_one, L'.one_mul] at this
  exact this

end ExtraLevelTransport

open ExtraLevelTransport in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (E E' : FakeEllipticCurve Λ N S) (h : FakeEllipticCurve.Iso E' E) (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      FakeEllipticCurve.WithExtraLevel.Iso (⟨E', K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨E, K⟩ := by
  obtain ⟨e, he, hmul_e, hact_e, hlev_e⟩ := h
  have he' : e.inv ≫ E'.f = E.f := by rw [Iso.inv_comp_eq, he]

  have hround : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt e.hom he (mapPt e.inv he' P) = P :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hround' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      mapPt e.inv he' (mapPt e.hom he P) = P :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id])

  have hmul_einv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.inv he' (E.L.mul t P Q) = E'.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
    intro T t P Q
    have h := hmul_e t (mapPt e.inv he' P) (mapPt e.inv he' Q)
    rw [hround, hround] at h
    rw [← h, hround']

  have hFT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (K'.levK ≫ e.hom) P ↔ FactorsThrough K'.levK (mapPt e.inv he' P) := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      exact ⟨P₀, by rw [mapPt_coe, ← hP₀]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    · rintro ⟨P₀, hP₀⟩
      refine ⟨P₀, ?_⟩
      rw [mapPt_coe] at hP₀
      rw [← Category.assoc, hP₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hFT' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E'.f),
      FactorsThrough K'.levK P ↔ FactorsThrough (K'.levK ≫ e.hom) (mapPt e.hom he P) := by
    intro T t P
    rw [hFT, hround']
  have hcomp : (K'.levK ≫ e.hom) ≫ E.f = K'.levK ≫ E'.f := by rw [Category.assoc, he]

  refine ⟨{ K := K'.K
            levK := K'.levK ≫ e.hom
            levK_closed := ?_
            levK_sub := ?_
            levK_one := ?_
            levK_torsion := ?_
            levK_stable := ?_
            levK_disjoint := ?_
            levK_finite := ?_
            levK_flat := ?_
            levK_finitePresentation := ?_
            levK_rank := ?_
            levK_fibre := ?_ }, ?_⟩
  · haveI := K'.levK_closed
    infer_instance
  · intro T t P Q hP hQ
    rw [hFT] at hP hQ
    obtain ⟨h1, h2⟩ := K'.levK_sub t _ _ hP hQ
    refine ⟨?_, ?_⟩
    · rw [hFT, hmul_einv]; exact h1
    · rw [hFT, map_inv_of_hom E.L E'.L e.inv he' hmul_einv]; exact h2
  · intro T t
    rw [hFT, map_one_of_hom E.L E'.L e.inv he' hmul_einv]
    exact K'.levK_one t
  · intro T t P hP
    rw [hFT] at hP
    have h := K'.levK_torsion t _ hP
    rw [← map_nsmulPt_of_hom E.L E'.L e.inv he' hmul_einv] at h
    have h2 := congrArg (mapPt e.hom he) h
    rw [hround, map_one_of_hom E'.L E.L e.hom he hmul_e] at h2
    exact h2
  · intro x T t P hP
    rw [hFT] at hP ⊢
    have h := K'.levK_stable x t _ hP

    have hx : E.act x ≫ e.inv = e.inv ≫ E'.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hact_e]
    have : mapPt e.inv he' (pushPt (E.act x) (E.act_over x) P) = pushPt (E'.act x) (E'.act_over x) (mapPt e.inv he' P) :=
      Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, hx])
    rw [this]; exact h
  · intro T t P hP hlev
    rw [hFT] at hP
    have hlev' : FactorsThrough E'.lev (mapPt e.inv he' P) := by
      have := (hlev_e t (mapPt e.inv he' P)).mpr
      rw [hround] at this
      exact this hlev
    have h := K'.levK_disjoint t _ hP hlev'
    have h2 := congrArg (mapPt e.hom he) h
    rw [hround, map_one_of_hom E'.L E.L e.hom he hmul_e] at h2
    exact h2
  · rw [hcomp]; exact K'.levK_finite
  · rw [hcomp]; exact K'.levK_flat
  · rw [hcomp]; exact K'.levK_finitePresentation
  · intro s; rw [hcomp]; exact K'.levK_rank s
  · intro k _ _ sk hℓ
    obtain ⟨eK, heK⟩ := K'.levK_fibre k sk hℓ

    let toE : {P : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough K'.levK P} →
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (K'.levK ≫ e.hom) P} :=
      fun P => ⟨mapPt e.hom he P.1, (hFT' _ P.1).mp P.2⟩
    let toE' : {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (K'.levK ≫ e.hom) P} →
        {P : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough K'.levK P} :=
      fun P => ⟨mapPt e.inv he' P.1, (hFT _ P.1).mp P.2⟩
    let eE : {P : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough K'.levK P} ≃
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (K'.levK ≫ e.hom) P} :=
      { toFun := toE, invFun := toE',
        left_inv := fun P => Subtype.ext (hround' _ P.1),
        right_inv := fun P => Subtype.ext (hround _ P.1) }
    refine ⟨eK.trans eE, fun x y => ?_⟩
    show (mapPt e.hom he (eK (x + y)).1) = E.L.mul _ (mapPt e.hom he (eK x).1) (mapPt e.hom he (eK y).1)
    rw [heK, hmul_e]
  ·
    exact ⟨e, he, hmul_e, hact_e, hlev_e, fun t P => hFT' t P⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso (solution)
