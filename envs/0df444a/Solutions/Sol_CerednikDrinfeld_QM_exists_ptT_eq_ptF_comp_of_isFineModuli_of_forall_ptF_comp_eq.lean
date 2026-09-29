-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ed3e7c26-23fb-59b7-b315-9f15953332ef

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion TensorProduct

noncomputable section

namespace FppfPtT12

section General

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s')
    {P Q : SchemeHomOver s f} {P' Q' : SchemeHomOver s' f} (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul s P Q).1 = (L.mul s' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

end General

def Lin {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (m ℓ : ℕ)
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
    FactorsThrough K.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P k sk)) = Q

section PB

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ}

theorem wel_isPullback_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] {φ : S →+* S'} {ψ : S' →+* S''}
    {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S} {u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'}
    {u'' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S''}
    (h' : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u') (h'' : FakeEllipticCurve.WithExtraLevel.IsPullback ψ u' u'') :
    FakeEllipticCurve.WithExtraLevel.IsPullback (ψ.comp φ) u u'' := by
  obtain ⟨g', hg', hmul', hact', hlev'⟩ := h'
  obtain ⟨g'', hg'', hmul'', hact'', hlev''⟩ := h''
  have hb : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hsq : IsPullback (g'' ≫ g') u''.1.f u.1.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hb]; exact hg''.paste_horiz hg'
  refine ⟨g'' ≫ g', hsq, ?_, ?_, ?_⟩
  · intro T t'' P Q
    have hbT : (t'' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom φ) =
        t'' ≫ Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by rw [hb, Category.assoc]
    rw [← Category.assoc, hmul'', hmul']
    exact mul_val_congr u.1.L hbT (Category.assoc _ _ _) (Category.assoc _ _ _)
  · intro x
    rw [← Category.assoc, hact'', Category.assoc, hact', Category.assoc]
  · intro T t'' P
    constructor
    · intro hP
      obtain ⟨P₀', hP₀'⟩ := (hlev'' t'' P).1 hP
      obtain ⟨P₀, hP₀⟩ := (hlev' (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
        ⟨P.1 ≫ g'', by rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩).1 ⟨P₀', hP₀'⟩
      exact ⟨P₀, by rw [hP₀, Category.assoc]⟩
    · intro hP
      obtain ⟨P₀', hP₀'⟩ := (hlev'' t'' P).2 hP
      obtain ⟨P₀, hP₀⟩ := (hlev' (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
        ⟨P.1 ≫ g'', by rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩).2 ⟨P₀', hP₀'⟩
      exact ⟨P₀, by rw [hP₀, Category.assoc]⟩

theorem wel_isPullback_of_iso {S S' : Type} [CommRing S] [CommRing S'] {ψ : S →+* S'}
    {u u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S} {w : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'}
    (hiso : FakeEllipticCurve.WithExtraLevel.Iso u u₂) (h : FakeEllipticCurve.WithExtraLevel.IsPullback ψ u₂ w) :
    FakeEllipticCurve.WithExtraLevel.IsPullback ψ u w := by
  obtain ⟨e, he, hmul_e, hact_e, hlev_e, hlevK_e⟩ := hiso
  obtain ⟨g, hg, hmul, hact, hlev⟩ := h
  have he' : e.inv ≫ u.1.f = u₂.1.f := by rw [← he, e.inv_hom_id_assoc]
  have hsqe : IsPullback e.inv u₂.1.f u.1.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  have hsq : IsPullback (g ≫ e.inv) w.1.f u.1.f (Spec.map (CommRingCat.ofHom ψ)) := by
    have := hg.paste_horiz hsqe
    rwa [Category.comp_id] at this
  have hmul_inv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₂.1.f),
      mapPt e.inv he' (u₂.1.L.mul t P Q) = u.1.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
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
    exact mul_val_congr u.1.L rfl (Category.assoc _ _ _) (Category.assoc _ _ _)
  · intro x
    have hx : u₂.1.act x ≫ e.inv = e.inv ≫ u.1.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (hact_e x).symm
    rw [← Category.assoc, hact, Category.assoc, hx, Category.assoc]
  · intro T t' P
    let R : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom ψ)) u.1.f :=
      ⟨P.1 ≫ g ≫ e.inv, by rw [Category.assoc, hsq.w, ← Category.assoc, P.2]⟩
    constructor
    · intro hP
      obtain ⟨P₀₂, hP₀₂⟩ := (hlev t' P).1 hP
      have hR : FactorsThrough u₂.1.lev (mapPt e.hom he R) :=
        ⟨P₀₂, by rw [hP₀₂]; simp [mapPt, R]⟩
      obtain ⟨P₀, hP₀⟩ := (hlev_e _ R).mpr hR
      exact ⟨P₀, hP₀⟩
    · intro hP
      obtain ⟨P₀₂, hP₀₂⟩ := (hlev t' P).2 hP
      have hR : FactorsThrough u₂.2.levK (mapPt e.hom he R) :=
        ⟨P₀₂, by rw [hP₀₂]; simp [mapPt, R]⟩
      obtain ⟨P₀, hP₀⟩ := (hlevK_e _ R).mpr hR
      exact ⟨P₀, hP₀⟩

theorem wel_isPullback_id {S : Type} [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    FakeEllipticCurve.WithExtraLevel.IsPullback (RingHom.id S) u u := by
  have hb : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  have hsq : IsPullback (𝟙 u.1.A) u.1.f u.1.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hb]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨𝟙 _, hsq, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [Category.comp_id]
    exact mul_val_congr u.1.L (by rw [hb, Category.comp_id]) (Category.comp_id _).symm (Category.comp_id _).symm
  · intro x; simp
  · intro T t P
    constructor
    · rintro ⟨P₀, h⟩; exact ⟨P₀, by rw [h, Category.comp_id]⟩
    · rintro ⟨P₀, h⟩; exact ⟨P₀, by rw [h, Category.comp_id]⟩

end PB

section Transport

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ m : ℕ} (L₀ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type} [CommRing S]

theorem exists_fullLevel_iso_lin (u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (hiso : FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂) (P₁ : u₁.1.FullLevel m)
    (hlin : Lin L₀ m ℓ u₁.1 u₁.2 P₁.P) :
    ∃ P₂ : u₂.1.FullLevel m,
      FakeEllipticCurve.WithFullLevel.Iso (⟨u₁.1, P₁⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) ⟨u₂.1, P₂⟩ ∧
      Lin L₀ m ℓ u₂.1 u₂.2 P₂.P := by
  obtain ⟨e, he, hmul, hact, hlev, hlevK⟩ := hiso
  have he' : e.inv ≫ u₁.1.f = u₂.1.f := by rw [← he, e.inv_hom_id_assoc]

  have hφψ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q : SchemeHomOver t u₂.1.f),
      mapPt e.hom he (mapPt e.inv he' Q) = Q := fun Q => Subtype.ext (by simp [mapPt])
  have hψφ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u₁.1.f),
      mapPt e.inv he' (mapPt e.hom he P) = P := fun P => Subtype.ext (by simp [mapPt])
  have hinj : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P Q : SchemeHomOver t u₁.1.f),
      mapPt e.hom he P = mapPt e.hom he Q → P = Q := fun P Q h => by rw [← hψφ P, h, hψφ]

  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.hom he (u₁.1.L.one t) = u₂.1.L.one t := by
    intro T t
    letI := u₂.1.L.pointGroup t
    have h := hmul t (u₁.1.L.one t) (u₁.1.L.one t)
    rw [u₁.1.L.one_mul] at h
    have : mapPt e.hom he (u₁.1.L.one t) * mapPt e.hom he (u₁.1.L.one t) = mapPt e.hom he (u₁.1.L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have hnsmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t u₁.1.f),
      mapPt e.hom he (nsmulPt u₁.1.L t n P) = nsmulPt u₂.1.L t n (mapPt e.hom he P) := by
    intro T t n P
    induction n with
    | zero => exact hone t
    | succ n ih =>
      show mapPt e.hom he (u₁.1.L.mul t (nsmulPt u₁.1.L t n P) P) = u₂.1.L.mul t (nsmulPt u₂.1.L t n (mapPt e.hom he P)) _
      rw [hmul, ih]
  have hone' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), mapPt e.inv he' (u₂.1.L.one t) = u₁.1.L.one t :=
    fun t => by rw [← hone t, hψφ]
  have hnsmul' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (Q : SchemeHomOver t u₂.1.f),
      mapPt e.inv he' (nsmulPt u₂.1.L t n Q) = nsmulPt u₁.1.L t n (mapPt e.inv he' Q) := by
    intro T t n Q
    apply hinj
    rw [hφψ, hnsmul, hφψ]

  have hact' : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (x : ↥Λ) (P : SchemeHomOver t u₁.1.f),
      mapPt e.hom he (pushPt (u₁.1.act x) (u₁.1.act_over x) P) =
        pushPt (u₂.1.act x) (u₂.1.act_over x) (mapPt e.hom he P) :=
    fun x P => Subtype.ext (by simp only [mapPt_coe, Category.assoc, hact x])
  have hsec : ∀ (k : Type) [Field k] (sk : S →+* k) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) u₁.1.f),
      FakeEllipticCurve.sectionAt (mapPt e.hom he P) k sk = mapPt e.hom he (FakeEllipticCurve.sectionAt P k sk) :=
    fun k _ sk P => Subtype.ext (by simp [FakeEllipticCurve.sectionAt, mapPt])
  refine ⟨{ P := mapPt e.hom he P₁.P, torsion := ?_, generates := ?_, annihilator := ?_ },
    ⟨e, he, hmul, hact, hlev, rfl⟩, ?_⟩
  · rw [← hnsmul, P₁.torsion, hone]
  · intro k _ _ sk Q hQ
    have hQ' : nsmulPt u₁.1.L (geomPoint k sk) m (mapPt e.inv he' Q) = u₁.1.L.one _ := by rw [← hnsmul', hQ, hone']
    obtain ⟨x, hx⟩ := P₁.generates k sk _ hQ'
    exact ⟨x, by rw [hsec, ← hact', hx, hφψ]⟩
  · intro k _ _ sk x
    rw [hsec, ← hact', ← P₁.annihilator k sk x, ← hone (geomPoint k sk)]
    exact ⟨fun h => hinj _ _ h, fun h => by rw [h]⟩
  · intro k _ _ sk Q
    have hQ : mapPt e.hom he (mapPt e.inv he' Q) = Q := hφψ Q
    rw [← hQ, ← hlevK _ (mapPt e.inv he' Q), hlin k sk (mapPt e.inv he' Q)]
    refine exists_congr (fun x => and_congr_right (fun _ => ?_))
    show _ ↔ pushPt (u₂.1.act x) (u₂.1.act_over x) (nsmulPt u₂.1.L (geomPoint k sk) (m / ℓ)
      (FakeEllipticCurve.sectionAt (mapPt e.hom he P₁.P) k sk)) = _
    rw [hsec, ← hnsmul, ← hact']
    exact ⟨fun h => by rw [h], fun h => hinj _ _ h⟩

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

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ} (L₀ : Submodule ℤ ℍ[ℚ, a, b]) {𝒪 : Type} [CommRing 𝒪]
  {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
  (hM : IsFineModuli Λ N m M πM ptF) {Y : Scheme.{0}} (π : M ⟶ Y)
  (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ) (P P' : E.FullLevel m),
    Lin L₀ m ℓ E K P.P → Lin L₀ m ℓ E K P'.P → (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

include hM hinvP in

theorem ptF_comp_eq_of_isPullback
    {S R : Type} [CommRing S] [CommRing R] (ψ : S →+* R) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪)) (w₁ w₂ : FakeEllipticCurve.WithFullLevel Λ N m R)
    (K₁ : w₁.1.ExtraLevel ℓ) (K₂ : w₂.1.ExtraLevel ℓ)
    (hl₁ : Lin L₀ m ℓ w₁.1 K₁ w₁.2.P) (hl₂ : Lin L₀ m ℓ w₂.1 K₂ w₂.2.P)
    (h₁ : FakeEllipticCurve.WithExtraLevel.IsPullback ψ u ⟨w₁.1, K₁⟩)
    (h₂ : FakeEllipticCurve.WithExtraLevel.IsPullback ψ u ⟨w₂.1, K₂⟩) :
    (ptF R r w₁).1 ≫ π = (ptF R r w₂).1 ≫ π := by
  have hiso := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isPullback_of_isPullback ψ u
    ⟨w₁.1, K₁⟩ ⟨w₂.1, K₂⟩ h₁ h₂
  obtain ⟨P₂', hI, hl₂'⟩ := exists_fullLevel_iso_lin L₀ (⟨w₁.1, K₁⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ R)
    ⟨w₂.1, K₂⟩ hiso w₁.2 hl₁
  have h3 : ptF R r w₁ = ptF R r ⟨w₂.1, P₂'⟩ := hM.ptF_iso R r w₁ ⟨w₂.1, P₂'⟩ hI
  rw [h3]
  exact hinvP R r w₂.1 K₂ w₂.2 P₂' hl₂ hl₂'

private structure _root_.FppfPtT12.Cover (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (m : ℕ) (S : Type) [CommRing S]
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) : Type 1 where

  S' : Type
  [inst : CommRing S']

  φ : S →+* S'
  ff : φ.FaithfullyFlat

  w' : FakeEllipticCurve.WithFullLevel Λ N m S'

  K' : w'.1.ExtraLevel ℓ
  pb : FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩

  lin : Lin L₀ m ℓ w'.1 K' w'.2.P

p2m_export "FppfPtT12" "Cover"
p2m_export_all "FppfPtT12" "Cover"
attribute [scoped instance] Cover.inst

variable {S : Type} [CommRing S]

scoped instance epi_cover {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S} (c : Cover L₀ m S u) :
    Epi (Spec.map (CommRingCat.ofHom c.φ)) := by
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  infer_instance

include hM hinvP in

theorem descent_affine (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S}
    (c : Cover L₀ m S u) {R : CommRingCat.{0}} (g₁ g₂ : Spec R ⟶ Spec (CommRingCat.of c.S'))
    (h : g₁ ≫ Spec.map (CommRingCat.ofHom c.φ) = g₂ ≫ Spec.map (CommRingCat.ofHom c.φ)) :
    g₁ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.w').1 ≫ π =
      g₂ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.w').1 ≫ π := by
  set τ₁ : c.S' →+* R := (Spec.preimage g₁).hom with hτ₁
  set τ₂ : c.S' →+* R := (Spec.preimage g₂).hom with hτ₂
  have hg₁ : Spec.map (CommRingCat.ofHom τ₁) = g₁ := by rw [hτ₁, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg₂ : Spec.map (CommRingCat.ofHom τ₂) = g₂ := by rw [hτ₂, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hτ : τ₁.comp c.φ = τ₂.comp c.φ := by
    have h' : Spec.map (CommRingCat.ofHom (τ₁.comp c.φ)) = Spec.map (CommRingCat.ofHom (τ₂.comp c.φ)) := by
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, hg₁, hg₂, h]
    have h'' := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
    simpa using h''

  obtain ⟨w₁, K₁, hw₁, hK₁, hl₁⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
      m ℓ L₀ τ₁ c.w' c.K'
  obtain ⟨w₂, K₂, hw₂, hK₂, hl₂⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
      m ℓ L₀ τ₂ c.w' c.K'
  have h₁ : FakeEllipticCurve.WithExtraLevel.IsPullback (τ₁.comp c.φ) u ⟨w₁.1, K₁⟩ := wel_isPullback_comp c.pb hK₁
  have h₂ : FakeEllipticCurve.WithExtraLevel.IsPullback (τ₁.comp c.φ) u ⟨w₂.1, K₂⟩ := by
    rw [hτ]; exact wel_isPullback_comp c.pb hK₂
  let r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪) :=
    Spec.map (CommRingCat.ofHom τ₁) ≫ Spec.map (CommRingCat.ofHom c.φ) ≫ s
  have hD := ptF_comp_eq_of_isPullback L₀ hM π hinvP (τ₁.comp c.φ) u r w₁ w₂ K₁ K₂ (hl₁ c.lin) (hl₂ c.lin) h₁ h₂
  have hr₂ : Spec.map (CommRingCat.ofHom τ₂) ≫ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) = r := by
    change _ = Spec.map (CommRingCat.ofHom τ₁) ≫ Spec.map (CommRingCat.ofHom c.φ) ≫ s
    rw [← Category.assoc, ← Category.assoc, hg₁, hg₂, h]
  have hp₁ := hM.ptF_pullback c.S' R τ₁ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) r rfl c.w' w₁ hw₁
  have hp₂ := hM.ptF_pullback c.S' R τ₂ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) r hr₂ c.w' w₂ hw₂
  rw [hp₁, hp₂, Category.assoc, Category.assoc, hg₁, hg₂] at hD
  exact hD

include hM hinvP in

theorem descent_condition (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S}
    (c : Cover L₀ m S u) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of c.S'))
    (h : g₁ ≫ Spec.map (CommRingCat.ofHom c.φ) = g₂ ≫ Spec.map (CommRingCat.ofHom c.φ)) :
    g₁ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.w').1 ≫ π =
      g₂ ≫ (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.w').1 ≫ π := by
  apply Scheme.Cover.hom_ext Z.affineCover
  intro i
  rw [← Category.assoc, ← Category.assoc (Z.affineCover.f i)]
  exact descent_affine L₀ hM π hinvP s c (Z.affineCover.f i ≫ g₁) (Z.affineCover.f i ≫ g₂)
    (by simp only [Category.assoc, h])

def xOf (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S}
    (c : Cover L₀ m S u) : Spec (CommRingCat.of S) ⟶ Y :=
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  EffectiveEpi.desc (Spec.map (CommRingCat.ofHom c.φ)) ((ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.w').1 ≫ π)
    (fun g₁ g₂ h => descent_condition L₀ hM π hinvP s c g₁ g₂ h)

private theorem _root_.FppfPtT12.fac (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S}
    (c : Cover L₀ m S u) :
    Spec.map (CommRingCat.ofHom c.φ) ≫ xOf L₀ hM π hinvP s c =
      (ptF c.S' (Spec.map (CommRingCat.ofHom c.φ) ≫ s) c.w').1 ≫ π := by
  haveI := flat_of_faithfullyFlat c.ff
  haveI := surjective_of_faithfullyFlat c.ff
  exact EffectiveEpi.fac _ _ _

p2m_export "FppfPtT12" "fac"
include hM hinvP in

theorem key (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) {u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S}
    (c : Cover L₀ m S u) {T : Type} [CommRing T] (τ : S →+* T) (w : FakeEllipticCurve.WithFullLevel Λ N m T)
    (K : w.1.ExtraLevel ℓ) (hl : Lin L₀ m ℓ w.1 K w.2.P)
    (hw : FakeEllipticCurve.WithExtraLevel.IsPullback τ u ⟨w.1, K⟩) :
    Spec.map (CommRingCat.ofHom τ) ≫ xOf L₀ hM π hinvP s c = (ptF T (Spec.map (CommRingCat.ofHom τ) ≫ s) w).1 ≫ π := by
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

  obtain ⟨wR, KR, hwR, hKR, hlR⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
      m ℓ L₀ κT w K
  obtain ⟨uR, KuR, huR, hKuR, hluR⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
      m ℓ L₀ κ₁ c.w' c.K'
  have h₁ : FakeEllipticCurve.WithExtraLevel.IsPullback (κT.comp τ) u ⟨wR.1, KR⟩ := wel_isPullback_comp hw hKR
  have h₂ : FakeEllipticCurve.WithExtraLevel.IsPullback (κT.comp τ) u ⟨uR.1, KuR⟩ := by
    rw [hκ]; exact wel_isPullback_comp c.pb hKuR
  let r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of 𝒪) :=
    Spec.map (CommRingCat.ofHom κT) ≫ Spec.map (CommRingCat.ofHom τ) ≫ s
  have hD := ptF_comp_eq_of_isPullback L₀ hM π hinvP (κT.comp τ) u r wR uR KR KuR (hlR hl) (hluR c.lin) h₁ h₂
  have hp₁ := hM.ptF_pullback T R κT (Spec.map (CommRingCat.ofHom τ) ≫ s) r rfl w wR hwR
  have hr : Spec.map (CommRingCat.ofHom κ₁) ≫ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) = r := by
    change _ = Spec.map (CommRingCat.ofHom κT) ≫ Spec.map (CommRingCat.ofHom τ) ≫ s
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hκ]
  have hp₂ := hM.ptF_pullback c.S' R κ₁ (Spec.map (CommRingCat.ofHom c.φ) ≫ s) r hr c.w' uR huR
  rw [hp₁, hp₂, Category.assoc, Category.assoc] at hD

  rw [← cancel_epi (Spec.map (CommRingCat.ofHom κT)), hD, ← fac L₀ hM π hinvP s c, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ]

variable (hm𝒪 : IsUnit ((m : ℕ) : 𝒪))
  (hloc : ∀ (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), IsUnit ((m : ℕ) : S) →
    ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩ ∧ Lin L₀ m ℓ w'.1 K' w'.2.P)

include hm𝒪 hloc in

theorem nonempty_cover (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    Nonempty (Cover L₀ m S u) := by
  have hunit : IsUnit ((m : ℕ) : S) := by
    have h := hm𝒪.map (Spec.preimage s).hom
    rwa [map_natCast] at h
  obtain ⟨S', inst, φ, hflat, hsurj, w', K', hpb, hlin⟩ := hloc S u hunit
  exact ⟨{ S' := S', φ := φ, ff := faithfullyFlat_of_flat_of_surjective φ hflat hsurj, w' := w', K' := K', pb := hpb, lin := hlin }⟩

def cov (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    Cover L₀ m S u :=
  Classical.choice (nonempty_cover L₀ hm𝒪 hloc s u)

variable {πY : Y ⟶ Spec (CommRingCat.of 𝒪)}

def ptT (hπ : π ≫ πY = πM) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) : SchemeHomOver s πY :=
  ⟨xOf L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s u), by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (cov L₀ hm𝒪 hloc s u).φ)), ← Category.assoc, fac, Category.assoc, hπ]
    exact (ptF _ _ _).2⟩

include hM hinvP hm𝒪 hloc in
theorem main (hπ : π ≫ πY = πM) :
    ∃ ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ),
        Lin L₀ m ℓ w.1 K w.2.P → (ptT S s ⟨w.1, K⟩).1 = (ptF S s w).1 ≫ π) := by
  refine ⟨ptT L₀ hM π hinvP hm𝒪 hloc hπ, ?_, ?_, ?_⟩
  ·
    intro S _ s u u' hiso
    apply Subtype.ext
    change xOf L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s u) = xOf L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s u')
    set c' := cov L₀ hm𝒪 hloc s u'
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom c'.φ)), fac L₀ hM π hinvP s c']
    exact key L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s u) c'.φ c'.w' c'.K' c'.lin (wel_isPullback_of_iso hiso c'.pb)
  ·
    intro S S' _ _ φ s s' hss' u u' huu'
    change xOf L₀ hM π hinvP s' (cov L₀ hm𝒪 hloc s' u') =
      Spec.map (CommRingCat.ofHom φ) ≫ xOf L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s u)
    set c' := cov L₀ hm𝒪 hloc s' u'
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom c'.φ)), fac L₀ hM π hinvP s' c', ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp,
      key L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s u) (c'.φ.comp φ) c'.w' c'.K' c'.lin (wel_isPullback_comp huu' c'.pb)]
    have hb : Spec.map (CommRingCat.ofHom (c'.φ.comp φ)) ≫ s = Spec.map (CommRingCat.ofHom c'.φ) ≫ s' := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hss']
    rw [hb]
  ·
    intro S _ s w K hlin
    change xOf L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s ⟨w.1, K⟩) = (ptF S s w).1 ≫ π
    have hk := key L₀ hM π hinvP s (cov L₀ hm𝒪 hloc s ⟨w.1, K⟩) (RingHom.id S) w K hlin (wel_isPullback_id _)
    have hb : Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ s = s := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [hb] at hk
    rwa [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at hk

end Descent

end FppfPtT12
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq.FppfPtT12"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq.FppfPtT12"

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {𝒪 : Type} [CommRing 𝒪] (hm𝒪 : IsUnit ((m : ℕ) : 𝒪))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF)
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ Y) (hπ : π ≫ πY = πM)

    (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ) (P P' : E.FullLevel m),
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q) →
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P'.P k sk)) = Q) →
      (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

    (hloc : ∀ (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), IsUnit ((m : ℕ) : S) →
      ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
        Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩ ∧
          ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) w'.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w'.1.act x) (w'.1.act_over x)
              (nsmulPt w'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w'.2.P k sk)) = Q) :
    ∃ ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        (ptT S s ⟨w.1, K⟩).1 = (ptF S s w).1 ≫ π) :=
  FppfPtT12.main L₀ hM π hinvP hm𝒪 hloc hπ

end S_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq (solution)
