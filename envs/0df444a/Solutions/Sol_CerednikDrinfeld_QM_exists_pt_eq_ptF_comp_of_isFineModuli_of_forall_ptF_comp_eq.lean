-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4845fe16-6969-53fd-b157-7618fdb11e42

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"

open scoped Quaternion TensorProduct

noncomputable section

namespace P2mKcFppfPt

section General

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    {P Q : SchemeHomOver s f} {P' Q' : SchemeHomOver s' f} (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul s P Q).1 = (L.mul s' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem nsmulPt_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x) =
      L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x)
    rw [L.mul_natural t t' ψ hψ, ih]

end General

section PB

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem isPullback_fst {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'} {m : ℕ}
    {u : FakeEllipticCurve.WithFullLevel Λ N m S} {u' : FakeEllipticCurve.WithFullLevel Λ N m S'}
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') : FakeEllipticCurve.IsPullback φ u.1 u'.1 := by
  obtain ⟨g, hg, hmul, hact, hlev, -⟩ := h
  exact ⟨g, hg, hmul, hact, hlev⟩

theorem isPullback_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] {φ : S →+* S'} {ψ : S' →+* S''}
    {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {E'' : FakeEllipticCurve Λ N S''}
    (h' : FakeEllipticCurve.IsPullback φ E E') (h'' : FakeEllipticCurve.IsPullback ψ E' E'') :
    FakeEllipticCurve.IsPullback (ψ.comp φ) E E'' := by
  obtain ⟨g', hg', hmul', hact', hlev'⟩ := h'
  obtain ⟨g'', hg'', hmul'', hact'', hlev''⟩ := h''
  have hb : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hsq : IsPullback (g'' ≫ g') E''.f E.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hb]; exact hg''.paste_horiz hg'
  refine ⟨g'' ≫ g', hsq, ?_, ?_, ?_⟩
  · intro T t'' P Q
    have hbT : (t'' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) =
        t'' ≫ Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by rw [hb, Category.assoc]
    rw [← Category.assoc, hmul'', hmul']
    exact mul_val_congr E.L hbT (Category.assoc _ _ _) (Category.assoc _ _ _)
  · intro x
    rw [← Category.assoc, hact'', Category.assoc, hact', Category.assoc]
  · intro T t'' P hP
    obtain ⟨P₀', hP₀'⟩ := hlev'' t'' P hP
    obtain ⟨P₀, hP₀⟩ := hlev' (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ g'', by rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩ ⟨P₀', hP₀'⟩
    exact ⟨P₀, by rw [hP₀, Category.assoc]⟩

theorem isPullback_of_iso {S S' : Type} [CommRing S] [CommRing S'] {ψ : S →+* S'}
    {E E₂ : FakeEllipticCurve Λ N S} {W : FakeEllipticCurve Λ N S'}
    (hiso : FakeEllipticCurve.Iso E E₂) (h : FakeEllipticCurve.IsPullback ψ E₂ W) :
    FakeEllipticCurve.IsPullback ψ E W := by
  obtain ⟨e, he, hmul_e, hact_e, hlev_e⟩ := hiso
  obtain ⟨g, hg, hmul, hact, hlev⟩ := h
  have he' : e.inv ≫ E.f = E₂.f := by rw [← he, e.inv_hom_id_assoc]
  have hsqe : IsPullback e.inv E₂.f E.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  have hsq : IsPullback (g ≫ e.inv) W.f E.f (Spec.map (CommRingCat.ofHom ψ)) := by
    have := hg.paste_horiz hsqe
    rwa [Category.comp_id] at this

  have hmul_inv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₂.f),
      mapPt e.inv he' (E₂.L.mul t P Q) = E.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
    intro T t P Q
    have hP : mapPt e.hom he (mapPt e.inv he' P) = P := Subtype.ext (by simp [mapPt])
    have hQ : mapPt e.hom he (mapPt e.inv he' Q) = Q := Subtype.ext (by simp [mapPt])
    conv_lhs => rw [← hP, ← hQ, ← hmul_e]
    exact Subtype.ext (by simp [mapPt])
  refine ⟨g ≫ e.inv, hsq, ?_, ?_, ?_⟩
  · intro T t' P Q
    rw [← Category.assoc, hmul]
    have h := congrArg Subtype.val (hmul_inv (t' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩)
    simp only [mapPt_coe] at h
    rw [h]
    exact mul_val_congr E.L rfl (Category.assoc _ _ _) (Category.assoc _ _ _)
  · intro x
    have hx : E₂.act x ≫ e.inv = e.inv ≫ E.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (hact_e x).symm
    rw [← Category.assoc, hact, Category.assoc, hx, Category.assoc]
  · intro T t' P hP
    obtain ⟨P₀₂, hP₀₂⟩ := hlev t' P hP
    let R : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom ψ)) E.f :=
      ⟨P.1 ≫ g ≫ e.inv, by rw [Category.assoc, hsq.w, ← Category.assoc, P.2]⟩
    have hR : FactorsThrough E₂.lev (mapPt e.hom he R) :=
      ⟨P₀₂, by rw [hP₀₂]; simp [mapPt, R]⟩
    obtain ⟨P₀, hP₀⟩ := (hlev_e _ R).mpr hR
    exact ⟨P₀, hP₀⟩

theorem isPullback_id {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsPullback (RingHom.id S) E E := by
  have hb : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  have hsq : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hb]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨𝟙 _, hsq, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [Category.comp_id]
    exact mul_val_congr E.L (by rw [hb, Category.comp_id]) (Category.comp_id _).symm (Category.comp_id _).symm
  · intro x; simp
  · intro T t P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [h, Category.comp_id]⟩

end PB

section Transport

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] {m : ℕ}

theorem exists_fullLevel_iso (u : FakeEllipticCurve.WithFullLevel Λ N m S) (E₂ : FakeEllipticCurve Λ N S)
    (hiso : FakeEllipticCurve.Iso u.1 E₂) :
    ∃ P₂ : E₂.FullLevel m, FakeEllipticCurve.WithFullLevel.Iso u ⟨E₂, P₂⟩ := by
  obtain ⟨E, lv⟩ := u
  obtain ⟨e, he, hmul, hact, hlev⟩ := hiso
  have he' : e.inv ≫ E.f = E₂.f := by rw [← he, e.inv_hom_id_assoc]

  have hφψ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t E₂.f),
      mapPt e.hom he (mapPt e.inv he' Q) = Q := fun Q => Subtype.ext (by simp [mapPt])
  have hψφ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f),
      mapPt e.inv he' (mapPt e.hom he P) = P := fun P => Subtype.ext (by simp [mapPt])
  have hinj : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P Q : SchemeHomOver t E.f),
      mapPt e.hom he P = mapPt e.hom he Q → P = Q := fun P Q h => by rw [← hψφ P, h, hψφ]

  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.hom he (E.L.one t) = E₂.L.one t := by
    intro T t
    letI := E₂.L.pointGroup t
    have h := hmul t (E.L.one t) (E.L.one t)
    rw [E.L.one_mul] at h
    have : mapPt e.hom he (E.L.one t) * mapPt e.hom he (E.L.one t) = mapPt e.hom he (E.L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have hnsmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f),
      mapPt e.hom he (nsmulPt E.L t n P) = nsmulPt E₂.L t n (mapPt e.hom he P) := by
    intro T t n P
    induction n with
    | zero => exact hone t
    | succ n ih =>
      show mapPt e.hom he (E.L.mul t (nsmulPt E.L t n P) P) = E₂.L.mul t (nsmulPt E₂.L t n (mapPt e.hom he P)) _
      rw [hmul, ih]
  have hone' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.inv he' (E₂.L.one t) = E.L.one t :=
    fun t => by rw [← hone t, hψφ]
  have hnsmul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (Q : SchemeHomOver t E₂.f),
      mapPt e.inv he' (nsmulPt E₂.L t n Q) = nsmulPt E.L t n (mapPt e.inv he' Q) := by
    intro T t n Q
    apply hinj
    rw [hφψ, hnsmul, hφψ]

  have hact' : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (x : ↥Λ) (P : SchemeHomOver t E.f),
      mapPt e.hom he (pushPt (E.act x) (E.act_over x) P) = pushPt (E₂.act x) (E₂.act_over x) (mapPt e.hom he P) :=
    fun x P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hact x])
  have hsec : ∀ (k : Type) [Field k] (sk : S →+* k) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f),
      FakeEllipticCurve.sectionAt (mapPt e.hom he P) k sk = mapPt e.hom he (FakeEllipticCurve.sectionAt P k sk) :=
    fun k _ sk P => Subtype.ext (by simp [FakeEllipticCurve.sectionAt, mapPt])
  refine ⟨{ P := mapPt e.hom he lv.P, torsion := ?_, generates := ?_, annihilator := ?_ }, e, he, hmul, hact, hlev, rfl⟩
  · rw [← hnsmul, lv.torsion, hone]
  · intro k _ _ sk Q hQ
    have hQ' : nsmulPt E.L (geomPoint k sk) m (mapPt e.inv he' Q) = E.L.one _ := by rw [← hnsmul', hQ, hone']
    obtain ⟨x, hx⟩ := lv.generates k sk _ hQ'
    exact ⟨x, by rw [hsec, ← hact', hx, hφψ]⟩
  · intro k _ _ sk x
    rw [hsec, ← hact', ← lv.annihilator k sk x, ← hone (geomPoint k sk)]
    exact ⟨fun h => hinj _ _ h, fun h => by rw [h]⟩

end Transport

section FF

theorem faithfullyFlat_of_flat_of_surjective {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (hf : Flat (Spec.map (CommRingCat.ofHom φ))) (hs : Surjective (Spec.map (CommRingCat.ofHom φ))) :
    φ.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact ⟨HasRingHomProperty.Spec_iff.mp hf, hs.surj⟩

theorem flat_of_faithfullyFlat {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'} (h : φ.FaithfullyFlat) :
    Flat (Spec.map (CommRingCat.ofHom φ)) :=
  HasRingHomProperty.Spec_iff.mpr ((RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp h).1)

theorem surjective_of_faithfullyFlat {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'} (h : φ.FaithfullyFlat) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨(RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp h).2⟩

theorem faithfullyFlat_algebraMap_tensor {S S₁ T : Type} [CommRing S] [CommRing S₁] [CommRing T] [Algebra S S₁]
    [Algebra S T] (h : (algebraMap S S₁).FaithfullyFlat) : (algebraMap T (T ⊗[S] S₁)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h ⊢
  infer_instance

end FF

section Descent

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hM : IsFineModuli Λ N m M πM ptF) {X : Scheme.{0}} (π : M ⟶ X)
  (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m), (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

theorem ptF_comp_eq_of_isPullback (hM : IsFineModuli Λ N m M πM ptF) (π : M ⟶ X)
    (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m), (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)
    {S R : Type} [CommRing S] [CommRing R] (ψ : S →+* R) (E : FakeEllipticCurve Λ N S)
    (r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪)) (w₁ w₂ : FakeEllipticCurve.WithFullLevel Λ N m R)
    (h₁ : FakeEllipticCurve.IsPullback ψ E w₁.1) (h₂ : FakeEllipticCurve.IsPullback ψ E w₂.1) :
    (ptF R r w₁).1 ≫ π = (ptF R r w₂).1 ≫ π := by
  obtain ⟨E₂, Q₂⟩ := w₂
  obtain ⟨P₂, hP₂⟩ := exists_fullLevel_iso w₁ E₂
    (CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isPullback_of_isPullback ψ E w₁.1 E₂ h₁ h₂)
  rw [hM.ptF_iso R r w₁ ⟨E₂, P₂⟩ hP₂]
  exact hinvP R r E₂ Q₂ P₂

private structure _root_.P2mKcFppfPt.Cover (m : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) : Type 1 where

  S' : Type
  [inst : CommRing S']

  φ : S →+* S'
  ff : φ.FaithfullyFlat

  u' : FakeEllipticCurve.WithFullLevel Λ N m S'
  pb : FakeEllipticCurve.IsPullback φ E u'.1

p2m_export "P2mKcFppfPt" "Cover"
p2m_export_all "P2mKcFppfPt" "Cover"
attribute [scoped instance] Cover.inst

variable {S : Type} [CommRing S]

scoped instance epi_cover {E : FakeEllipticCurve Λ N S} (c : Cover m S E) : Epi (Spec.map (CommRingCat.ofHom c.φ)) := by
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  infer_instance

include hM hinvP in

theorem descent_affine (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {E : FakeEllipticCurve Λ N S}
    (c : Cover m S E) {R : CommRingCat.{0}} (g₁ g₂ : Spec R ⟶ Spec (CommRingCat.of c.S'))
    (h : g₁ ≫ Spec.map (CommRingCat.ofHom c.φ) = g₂ ≫ Spec.map (CommRingCat.ofHom c.φ)) :
    g₁ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π =
      g₂ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π := by
  set τ₁ : c.S' →+* R := (Spec.preimage g₁).hom with hτ₁
  set τ₂ : c.S' →+* R := (Spec.preimage g₂).hom with hτ₂
  have hg₁ : Spec.map (CommRingCat.ofHom τ₁) = g₁ := by rw [hτ₁, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg₂ : Spec.map (CommRingCat.ofHom τ₂) = g₂ := by rw [hτ₂, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hτ : τ₁.comp c.φ = τ₂.comp c.φ := by
    have h' : Spec.map (CommRingCat.ofHom (τ₁.comp c.φ)) = Spec.map (CommRingCat.ofHom (τ₂.comp c.φ)) := by
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, hg₁, hg₂, h]
    have h'' := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
    simpa using h''

  obtain ⟨w₁, hw₁⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback τ₁ c.u'
  obtain ⟨w₂, hw₂⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback τ₂ c.u'
  have h₁ : FakeEllipticCurve.IsPullback (τ₁.comp c.φ) E w₁.1 := isPullback_comp c.pb (isPullback_fst hw₁)
  have h₂ : FakeEllipticCurve.IsPullback (τ₁.comp c.φ) E w₂.1 := by
    rw [hτ]; exact isPullback_comp c.pb (isPullback_fst hw₂)
  let r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪) :=
    Spec.map (CommRingCat.ofHom τ₁) ≫ Spec.map (CommRingCat.ofHom c.φ) ≫ s
  have hD := ptF_comp_eq_of_isPullback hM π hinvP (τ₁.comp c.φ) E r w₁ w₂ h₁ h₂
  have hr₂ : Spec.map (CommRingCat.ofHom τ₂) ≫ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) = r := by
    change _ = Spec.map (CommRingCat.ofHom τ₁) ≫ Spec.map (CommRingCat.ofHom c.φ) ≫ s
    rw [← Category.assoc, ← Category.assoc, hg₁, hg₂, h]
  have hp₁ := hM.ptF_pullback c.S' R τ₁ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) r rfl c.u' w₁ hw₁
  have hp₂ := hM.ptF_pullback c.S' R τ₂ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) r hr₂ c.u' w₂ hw₂
  rw [hp₁, hp₂, Category.assoc, Category.assoc, hg₁, hg₂] at hD
  exact hD

include hM hinvP in

theorem descent_condition (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {E : FakeEllipticCurve Λ N S}
    (c : Cover m S E) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of c.S'))
    (h : g₁ ≫ Spec.map (CommRingCat.ofHom c.φ) = g₂ ≫ Spec.map (CommRingCat.ofHom c.φ)) :
    g₁ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π =
      g₂ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π := by
  apply Scheme.Cover.hom_ext Z.affineCover
  intro i
  rw [← Category.assoc, ← Category.assoc (Z.affineCover.f i)]
  exact descent_affine hM π hinvP s c (Z.affineCover.f i ≫ g₁) (Z.affineCover.f i ≫ g₂)
    (by simp only [Category.assoc, h])

def xOf (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {E : FakeEllipticCurve Λ N S} (c : Cover m S E) :
    Spec (CommRingCat.of S) ⟶ X :=
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  EffectiveEpi.desc (Spec.map (CommRingCat.ofHom c.φ)) ((ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π)
    (fun g₁ g₂ h => descent_condition hM π hinvP s c g₁ g₂ h)

private theorem _root_.P2mKcFppfPt.fac (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {E : FakeEllipticCurve Λ N S} (c : Cover m S E) :
    Spec.map (CommRingCat.ofHom c.φ) ≫ xOf hM π hinvP s c =
      (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.u').1 ≫ π := by
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  exact EffectiveEpi.fac _ _ _

p2m_export "P2mKcFppfPt" "fac"

theorem key (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {E : FakeEllipticCurve Λ N S} (c : Cover m S E)
    {T : Type} [CommRing T] (τ : S →+* T) (w : FakeEllipticCurve.WithFullLevel Λ N m T)
    (hw : FakeEllipticCurve.IsPullback τ E w.1) :
    Spec.map (CommRingCat.ofHom τ) ≫ xOf hM π hinvP s c = (ptF T (Spec.map (CommRingCat.ofHom τ) ≫ s) w).1 ≫ π := by
  letI : Algebra S T := τ.toAlgebra
  letI : Algebra S c.S' := c.φ.toAlgebra
  let R : Type := T ⊗[S] c.S'
  let κT : T →+* R := algebraMap T R
  let κ₁ : c.S' →+* R := (Algebra.TensorProduct.includeRight : c.S' →ₐ[S] R).toRingHom
  have hκ : κT.comp τ = κ₁.comp c.φ := by
    ext y
    change algebraMap T R (algebraMap S T y) = (Algebra.TensorProduct.includeRight : c.S' →ₐ[S] R) (algebraMap S c.S' y)
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  have hff : κT.FaithfullyFlat := faithfullyFlat_algebraMap_tensor (S := S) c.ff
  haveI := flat_of_faithfullyFlat hff
  haveI := surjective_of_faithfullyFlat hff

  obtain ⟨wR, hwR⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback κT w
  obtain ⟨uR, huR⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback κ₁ c.u'
  have h₁ : FakeEllipticCurve.IsPullback (κT.comp τ) E wR.1 := isPullback_comp hw (isPullback_fst hwR)
  have h₂ : FakeEllipticCurve.IsPullback (κT.comp τ) E uR.1 := by
    rw [hκ]; exact isPullback_comp c.pb (isPullback_fst huR)
  let r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪) :=
    Spec.map (CommRingCat.ofHom κT) ≫ Spec.map (CommRingCat.ofHom τ) ≫ s
  have hD := ptF_comp_eq_of_isPullback hM π hinvP (κT.comp τ) E r wR uR h₁ h₂
  have hp₁ := hM.ptF_pullback T R κT (Spec.map (CommRingCat.ofHom τ) ≫ s) r rfl w wR hwR
  have hr : Spec.map (CommRingCat.ofHom κ₁) ≫ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) = r := by
    change _ = Spec.map (CommRingCat.ofHom κT) ≫ Spec.map (CommRingCat.ofHom τ) ≫ s
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hκ]
  have hp₂ := hM.ptF_pullback c.S' R κ₁ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) r hr c.u' uR huR
  rw [hp₁, hp₂, Category.assoc, Category.assoc] at hD

  rw [← cancel_epi (Spec.map (CommRingCat.ofHom κT)), hD, ← fac hM π hinvP s c, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ]

variable (hm𝒪 : IsUnit ((m : ℕ) : 𝒪))
  (hloc : ∀ (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S), IsUnit ((m : ℕ) : S) →
    ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.IsPullback φ E u'.1)

include hm𝒪 hloc in

theorem nonempty_cover (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E : FakeEllipticCurve Λ N S) :
    Nonempty (Cover m S E) := by
  have hunit : IsUnit ((m : ℕ) : S) := by
    have h := hm𝒪.map (Spec.preimage s).hom
    rwa [map_natCast] at h
  obtain ⟨S', inst, φ, hflat, hsurj, u', hpb⟩ := hloc S E hunit
  exact ⟨{ S' := S', φ := φ, ff := faithfullyFlat_of_flat_of_surjective φ hflat hsurj, u' := u', pb := hpb }⟩

def cov (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E : FakeEllipticCurve Λ N S) : Cover m S E :=
  Classical.choice (nonempty_cover hm𝒪 hloc s E)

variable {πX : X ⟶ Spec (CommRingCat.of 𝒪)}

def pt (hπ : π ≫ πX = πM) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) : SchemeHomOver s πX :=
  ⟨xOf hM π hinvP s (cov hm𝒪 hloc s E), by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (cov hm𝒪 hloc s E).φ)), ← Category.assoc, fac, Category.assoc, hπ]
    exact (ptF _ _ _).2⟩

include hM hinvP hm𝒪 hloc in
theorem main (hπ : π ≫ πX = πM) :
    ∃ pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve Λ N S → SchemeHomOver s πX,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
          FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S), (pt S s w.1).1 = (ptF S s w).1 ≫ π) := by
  refine ⟨pt hM π hinvP hm𝒪 hloc hπ, ?_, ?_, ?_⟩
  ·
    intro S _ s E E' hiso
    apply Subtype.ext
    change xOf hM π hinvP s (cov hm𝒪 hloc s E) = xOf hM π hinvP s (cov hm𝒪 hloc s E')
    set c' := cov hm𝒪 hloc s E'
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom c'.φ)), fac hM π hinvP s c']
    exact key hM π hinvP s (cov hm𝒪 hloc s E) c'.φ c'.u' (isPullback_of_iso hiso c'.pb)
  ·
    intro S S' _ _ φ s s' hss' E E' hEE'
    change xOf hM π hinvP s' (cov hm𝒪 hloc s' E') = Spec.map (CommRingCat.ofHom φ) ≫ xOf hM π hinvP s (cov hm𝒪 hloc s E)
    set c' := cov hm𝒪 hloc s' E'
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom c'.φ)), fac hM π hinvP s' c', ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp,
      key hM π hinvP s (cov hm𝒪 hloc s E) (c'.φ.comp φ) c'.u' (isPullback_comp hEE' c'.pb)]
    have hb : Spec.map (CommRingCat.ofHom (c'.φ.comp φ)) ≫ s = Spec.map (CommRingCat.ofHom c'.φ) ≫ s' := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hss']
    rw [hb]
  ·
    intro S _ s w
    obtain ⟨E, P⟩ := w
    change xOf hM π hinvP s (cov hm𝒪 hloc s E) = (ptF S s ⟨E, P⟩).1 ≫ π
    have hk := key hM π hinvP s (cov hm𝒪 hloc s E) (RingHom.id S) ⟨E, P⟩ (isPullback_id E)
    have hb : Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ s = s := by rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [hb] at hk
    rwa [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at hk

end Descent

end P2mKcFppfPt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq.P2mKcFppfPt"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq.P2mKcFppfPt"

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {𝒪 : Type} [CommRing 𝒪] (hm𝒪 : IsUnit ((m : ℕ) : 𝒪))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ X) (hπ : π ≫ πX = πM)

    (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m), (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

    (hloc : ∀ (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S), IsUnit ((m : ℕ) : S) →
      ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
        Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.IsPullback φ E u'.1) :
    ∃ pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve Λ N S → SchemeHomOver s πX,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
          FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S), (pt S s w.1).1 = (ptF S s w).1 ≫ π) :=
  P2mKcFppfPt.main hM π hinvP hm𝒪 hloc hπ

end S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq (solution)
