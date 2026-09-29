-- Prove2me | solution 1 for CerednikDrinfeld.QM.RigidifiedPairClass.rel_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/44075e3d-abe9-55cf-a562-51a4322f1d16

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField Pointwise
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace Ws47RL

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : GoodReductionJacobian.RelativeGroupLaw S f) {T : Scheme.{0}} (t t' : T ⟶ Spec (CommRingCat.of S)) (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  rw [Subtype.ext hP, Subtype.ext hQ]

open CerednikDrinfeld.QM.FakeEllipticCurve in
theorem mapPt_hom_inv {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : mapPt i.inv hi' (mapPt i.hom hi P) = P :=
  Subtype.ext (by simp [mapPt])

theorem mapPt_inv_hom {R : Type} [CommRing R] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (i : A ≅ A') (hi : i.hom ≫ f' = f) (hi' : i.inv ≫ f = f') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f') : mapPt i.hom hi (mapPt i.inv hi' P) = P :=
  Subtype.ext (by simp [mapPt])

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isoVia_symm {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n : ℕ} {S : Type} [CommRing S]
    (u u' : WithFullLevel Λ N n S) (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f)
    (h : WithFullLevel.IsoVia u u' i hi) :
    ∃ hi' : i.symm.hom ≫ u.1.f = u'.1.f, WithFullLevel.IsoVia u' u i.symm hi' := by
  have hi' : i.inv ≫ u.1.f = u'.1.f := by rw [← hi, Iso.inv_hom_id_assoc]
  obtain ⟨hm, ha, hl, hP⟩ := h
  refine ⟨hi', ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    have := hm t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [mapPt_inv_hom, mapPt_inv_hom] at this
    show mapPt i.inv hi' (u'.1.L.mul t P Q) = u.1.L.mul t (mapPt i.inv hi' P) (mapPt i.inv hi' Q)
    rw [← this, mapPt_hom_inv]
  · intro x
    show u'.1.act x ≫ i.inv = i.inv ≫ u.1.act x
    rw [Iso.eq_inv_comp, ← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro T t P
    have := hl t (mapPt i.inv hi' P)
    rw [mapPt_inv_hom] at this
    exact this.symm
  · show mapPt i.inv hi' u'.2.P = u.2.P
    rw [← hP, mapPt_hom_inv]

theorem isUnit_natCast_of_not_dvd {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    {L : Type} [CommRing L] [Algebra 𝒪 L] (hπ : algebraMap 𝒪 L π = 0) :
    IsUnit ((N : ℕ) : L) := by
  have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
  have hrL : ((r : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap 𝒪 L), ← hc, map_mul, hπ, mul_zero]
  have hcop : IsCoprime ((r : ℕ) : ℤ) ((N : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (((Fact.out : r.Prime).coprime_iff_not_dvd).mpr hrN)
  have h2 := hcop.map (Int.castRingHom L)
  simp only [eq_intCast, Int.cast_natCast, hrL] at h2
  exact isCoprime_zero_left.mp h2

theorem isUnit_natCast_quot_of_not_dvd {r N : ℕ} [Fact r.Prime] (hrN : ¬ r ∣ N)
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    {L : Type} [CommRing L] [Algebra 𝒪 L] (hπ : algebraMap 𝒪 L π = 0) :
    IsUnit ((N : ℕ) : L ⧸ Ideal.span {algebraMap 𝒪 L π}) := by
  have := (isUnit_natCast_of_not_dvd hrN hunr hπ).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))
  simpa using this

theorem Spec_map_id (S : Type) [CommRing S] : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem exists_corr_symm
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B}
    (hNB : IsUnit ((N : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    {E E' : FakeEllipticCurve Λ N B} (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f)
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ ψ E')
    (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (hib : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (hibf : ib ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (huA : IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (huAg : uA ≫ ρ.gA = ρ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib' : ρ'.Eb.A ⟶ ρ.Eb.A) (_ : ib' ≫ ρ.gb = ρ'.gb ≫ i.symm.hom) (_ : ib' ≫ ρ.Eb.f = ρ'.Eb.f)
      (uA' : ρ.Ab.A ⟶ ρ'.Ab.A) (_ : IsPullbackVia (RingHom.id _) ρ'.Ab ρ.Ab uA') (_ : uA' ≫ ρ'.gA = ρ.gA)
      (i₂ j₂ : ℕ),
      ib' ≫ ρ.φ ≫ uA' ≫ ρ'.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hid := Spec_map_id (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  obtain ⟨hpb, -, -, -⟩ := ρ.isPullback_Eb
  obtain ⟨hpb', -, -, -⟩ := ρ'.isPullback_Eb
  have hi' : i.inv ≫ E.f = E'.f := by rw [← hi, Iso.inv_hom_id_assoc]

  have w : (ρ'.gb ≫ i.inv) ≫ E.f = ρ'.Eb.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) := by
    rw [Category.assoc, hi', hpb'.w]
  let ib' : ρ'.Eb.A ⟶ ρ.Eb.A := hpb.lift (ρ'.gb ≫ i.inv) ρ'.Eb.f w
  have hib'1 : ib' ≫ ρ.gb = ρ'.gb ≫ i.inv := hpb.lift_fst _ _ _
  have hib'2 : ib' ≫ ρ.Eb.f = ρ'.Eb.f := hpb.lift_snd _ _ _
  have hinv : ib' ≫ ib = 𝟙 _ := by
    apply hpb'.hom_ext
    · rw [Category.assoc, hib, ← Category.assoc, hib'1, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hibf, hib'2, Category.id_comp]

  obtain ⟨uA', huA'g, huA'f, huA'v⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
      _ hNB A₀ ρ'.Ab ρ'.gA ρ'.isPullback_Ab ρ.Ab ρ.gA ρ.isPullback_Ab
  obtain ⟨hpbA', -, -, -⟩ := ρ'.isPullback_Ab
  obtain ⟨huAw, -, -, -⟩ := id huA
  obtain ⟨huA'w, -, huA'act, -⟩ := id huA'v
  have hinvA : uA ≫ uA' = 𝟙 _ := by
    apply hpbA'.hom_ext
    · rw [Category.assoc, huA'g, huAg, Category.id_comp]
    · have h1 := huAw.w; have h2 := huA'w.w
      simp only [hid, Category.comp_id] at h1 h2
      rw [Category.assoc, h2, h1, Category.id_comp]
  refine ⟨ib', hib'1, hib'2, uA', huA'v, huA'g, j₁, i₁, ?_⟩

  have h := congrArg (fun z => ib' ≫ z ≫ uA') hcorr
  simp only [Category.assoc] at h
  rw [← Category.assoc ib' ib, hinv, Category.id_comp, huA'act, huA'act, ← Category.assoc uA uA', hinvA,
    Category.id_comp] at h
  exact h.symm

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isoVia_refl {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n : ℕ} {S : Type} [CommRing S]
    (u : WithFullLevel Λ N n S) :
    ∃ hi : (Iso.refl u.1.A).hom ≫ u.1.f = u.1.f, WithFullLevel.IsoVia u u (Iso.refl u.1.A) hi := by
  have e : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u.1.f)
      (hi : (Iso.refl u.1.A).hom ≫ u.1.f = u.1.f), mapPt (Iso.refl u.1.A).hom hi P = P :=
    fun P hi => Subtype.ext (by simp [mapPt])
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; rw [e, e, e]
  · intro x; simp
  · intro T t P; rw [e]
  · exact e _ _

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isPullbackVia_id_self {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by rw [hid]; infer_instance
  have hpb : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) :=
    IsPullback.of_horiz_isIso ⟨by rw [hid, Category.id_comp, Category.comp_id]⟩
  refine ⟨hpb, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [Category.comp_id]
    have ht : t = t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by rw [hid, Category.comp_id]
    exact Ws47RL.mul_val_congr E.L _ _ ht _ _ _ _ (by simp) (by simp)
  · intro x; simp
  · intro T t P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [Category.comp_id]; exact h⟩

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isoVia_trans {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n : ℕ} {S : Type} [CommRing S]
    (u u' u'' : WithFullLevel Λ N n S) (i : u.1.A ≅ u'.1.A) (j : u'.1.A ≅ u''.1.A)
    (hi : i.hom ≫ u'.1.f = u.1.f) (hj : j.hom ≫ u''.1.f = u'.1.f)
    (h : WithFullLevel.IsoVia u u' i hi) (h' : WithFullLevel.IsoVia u' u'' j hj) :
    ∃ hk : (i ≪≫ j).hom ≫ u''.1.f = u.1.f, WithFullLevel.IsoVia u u'' (i ≪≫ j) hk := by
  have hk : (i ≪≫ j).hom ≫ u''.1.f = u.1.f := by rw [Iso.trans_hom, Category.assoc, hj, hi]
  have e : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t u.1.f),
      mapPt (i ≪≫ j).hom hk P = mapPt j.hom hj (mapPt i.hom hi P) := fun P => Subtype.ext (by simp [mapPt])
  obtain ⟨hm, ha, hl, hP⟩ := h
  obtain ⟨hm', ha', hl', hP'⟩ := h'
  refine ⟨hk, ?_, ?_, ?_, ?_⟩
  · intro T t P Q; rw [e, e, e, hm, hm']
  · intro x; rw [Iso.trans_hom, ← Category.assoc, ha, Category.assoc, ha', Category.assoc]
  · intro T t P; rw [e]; exact (hl t P).trans (hl' t _)
  · rw [e, hP, hP']

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem isPullbackVia_id_comp {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E₁ E₂ E₃ : FakeEllipticCurve Λ N S) (u₁ : E₂.A ⟶ E₁.A) (u₂ : E₃.A ⟶ E₂.A)
    (h₁ : IsPullbackVia (RingHom.id S) E₁ E₂ u₁) (h₂ : IsPullbackVia (RingHom.id S) E₂ E₃ u₂) :
    IsPullbackVia (RingHom.id S) E₁ E₃ (u₂ ≫ u₁) := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨pb₁, hm₁, ha₁, hl₁⟩ := h₁
  obtain ⟨pb₂, hm₂, ha₂, hl₂⟩ := h₂
  have pb₁' : IsPullback u₁ E₂.f E₁.f (𝟙 _) := by simpa only [hid] using pb₁
  have pb₂' : IsPullback u₂ E₃.f E₂.f (𝟙 _) := by simpa only [hid] using pb₂
  have pb : IsPullback (u₂ ≫ u₁) E₃.f E₁.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hid]; simpa only [Category.comp_id] using pb₂'.paste_horiz pb₁'
  refine ⟨pb, ?_, ?_, ?_⟩
  · intro T t P Q
    have w : ∀ (R : SchemeHomOver t E₃.f), (R.1 ≫ u₂) ≫ E₂.f = (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S))) := fun R => by
      rw [Category.assoc, pb₂.w, ← Category.assoc, R.2]
    rw [← Category.assoc, hm₂ t P Q, hm₁ _ ⟨P.1 ≫ u₂, w P⟩ ⟨Q.1 ≫ u₂, w Q⟩]
    exact Ws47RL.mul_val_congr E₁.L _ _ (by rw [hid, Category.comp_id]) _ _ _ _ (by simp) (by simp)
  · intro x; rw [← Category.assoc, ha₂, Category.assoc, ha₁, Category.assoc]
  · intro T t P hP
    obtain ⟨P₂, hP₂⟩ := hl₂ t P hP
    have w : (P.1 ≫ u₂) ≫ E₂.f = (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
      rw [Category.assoc, pb₂.w, ← Category.assoc, P.2]
    obtain ⟨P₀, hP₀⟩ := hl₁ _ ⟨P.1 ≫ u₂, w⟩ ⟨P₂, hP₂⟩
    exact ⟨P₀, by rw [hP₀]; simp⟩

open CerednikDrinfeld.QM.FakeEllipticCurve in
theorem act_rpow_comp {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r m n : ℕ) :
    E.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (m + n) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have e : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) =
      ((((r ^ (m + n) : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← QuaternionAlgebra.coe_mul]; congr 1; push_cast; ring
  have hmem : ((((r ^ n : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := e ▸ hΛℤ _
  rw [← E.act_mul ⟨(((r ^ n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ hmem]
  congr 1
  exact Subtype.ext e

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem corr_comp {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E₁ E₂ E₃ : FakeEllipticCurve Λ N B}
    (ρ₁ : Rigidification r π A₀ ψ E₁) (ρ₂ : Rigidification r π A₀ ψ E₂) (ρ₃ : Rigidification r π A₀ ψ E₃)
    (ih : E₁.A ⟶ E₂.A) (jh : E₂.A ⟶ E₃.A)
    (ib₁ : ρ₁.Eb.A ⟶ ρ₂.Eb.A) (hib₁ : ib₁ ≫ ρ₂.gb = ρ₁.gb ≫ ih) (hib₁f : ib₁ ≫ ρ₂.Eb.f = ρ₁.Eb.f)
    (uA₁ : ρ₂.Ab.A ⟶ ρ₁.Ab.A) (huA₁ : IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₂.Ab uA₁) (huA₁g : uA₁ ≫ ρ₁.gA = ρ₂.gA)
    (i₁ j₁ : ℕ)
    (h₁ : ib₁ ≫ ρ₂.φ ≫ uA₁ ≫ ρ₁.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (ib₂ : ρ₂.Eb.A ⟶ ρ₃.Eb.A) (hib₂ : ib₂ ≫ ρ₃.gb = ρ₂.gb ≫ jh) (hib₂f : ib₂ ≫ ρ₃.Eb.f = ρ₂.Eb.f)
    (uA₂ : ρ₃.Ab.A ⟶ ρ₂.Ab.A) (huA₂ : IsPullbackVia (RingHom.id _) ρ₂.Ab ρ₃.Ab uA₂) (huA₂g : uA₂ ≫ ρ₂.gA = ρ₃.gA)
    (i₂ j₂ : ℕ)
    (h₂ : ib₂ ≫ ρ₃.φ ≫ uA₂ ≫ ρ₂.Ab.act ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ ρ₂.Ab.act ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ∃ (ib : ρ₁.Eb.A ⟶ ρ₃.Eb.A) (_ : ib ≫ ρ₃.gb = ρ₁.gb ≫ (ih ≫ jh)) (_ : ib ≫ ρ₃.Eb.f = ρ₁.Eb.f)
      (uA : ρ₃.Ab.A ⟶ ρ₁.Ab.A) (_ : IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₃.Ab uA) (_ : uA ≫ ρ₁.gA = ρ₃.gA)
      (i' j' : ℕ),
      ib ≫ ρ₃.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ i' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ j' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hcomp := Ws47RL.isPullbackVia_id_comp ρ₁.Ab ρ₂.Ab ρ₃.Ab uA₁ uA₂ huA₁ huA₂
  obtain ⟨-, -, hact₁, -⟩ := huA₁
  refine ⟨ib₁ ≫ ib₂, ?_, ?_, uA₂ ≫ uA₁, hcomp, ?_, i₂ + i₁, j₁ + j₂, ?_⟩
  · rw [Category.assoc, hib₂, ← Category.assoc, hib₁, Category.assoc]
  · rw [Category.assoc, hib₂f, hib₁f]
  · rw [Category.assoc, huA₁g, huA₂g]
  · rw [← Ws47RL.act_rpow_comp hΛℤ ρ₁.Ab r i₂ i₁, ← Ws47RL.act_rpow_comp hΛℤ ρ₁.Ab r j₁ j₂]
    simp only [Category.assoc]
    rw [reassoc_of% (hact₁ ⟨(((r ^ i₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).symm, reassoc_of% h₂,
      reassoc_of% (hact₁ ⟨(((r ^ j₂ : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
      Ws47RL.act_rpow_comp hΛℤ ρ₁.Ab r j₂ i₁, Nat.add_comm j₂ i₁, ← Ws47RL.act_rpow_comp hΛℤ ρ₁.Ab r i₁ j₂,
      reassoc_of% h₁]

theorem transport
    {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)

    {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
    (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g))

    (hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
        (gu : u'.1.A ⟶ u.1.A) (hgu : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 gu)
        (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
        (u'.2.P).1 ≫ gu = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) gu hgu ρ ρ' →
          (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
            Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)

    (L L' : Type) [CommRing L] [Algebra C L] [Algebra 𝒪 L] [IsScalarTower 𝒪 C L]
    [CommRing L'] [Algebra C L'] [Algebra 𝒪 L'] [IsScalarTower 𝒪 C L'] (lam : L →ₐ[C] L')
    (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C L' (algebraMap 𝒪 C π) = 0)

    (d d' : ℕ) (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1)
    (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u'.1)
    (hd : ρ.d = d) (hd' : ρ'.d = d')
    (i₀ : u.1.A ≅ u'.1.A) (hi : i₀.hom ≫ u'.1.f = u.1.f) (hvia : FakeEllipticCurve.WithFullLevel.IsoVia u u' i₀ hi)
    (hcorr : (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i₀.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)) :
    ∃ (v v' : FakeEllipticCurve.WithFullLevel Λ N n L')
      (ς : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L').comp ψ) v.1)
      (ς' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L').comp ψ) v'.1)
      (hς : ς.d = d) (hς' : ς'.d = d')
      (j₀ : v.1.A ≅ v'.1.A) (hj : j₀.hom ≫ v'.1.f = v.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia v v' j₀ hj)
      (_ : (∃ (ib : ς.Eb.A ⟶ ς'.Eb.A) (_ : ib ≫ ς'.gb = ς.gb ≫ j₀.hom) (_ : ib ≫ ς'.Eb.f = ς.Eb.f)
        (uA : ς'.Ab.A ⟶ ς.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ς.Ab ς'.Ab uA) (_ : uA ≫ ς.gA = ς'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ς'.φ ≫ uA ≫ ς.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ς.φ ≫ ς.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
      (ptX d L' _ rfl v ς hς h0').1 = Spec.map (CommRingCat.ofHom (lam : L →+* L')) ≫ (ptX d L _ rfl u ρ hd h0).1 ∧
        (ptX d' L' _ rfl v' ς' hς' h0').1 = Spec.map (CommRingCat.ofHom (lam : L →+* L')) ≫ (ptX d' L _ rfl u' ρ' hd' h0).1 := by

  have hleg : (lam.restrictScalars 𝒪).comp ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) = (IsScalarTower.toAlgHom 𝒪 C L').comp ψ := by
    apply AlgHom.ext
    intro o
    show lam (algebraMap C L (ψ o)) = algebraMap C L' (ψ o)
    exact lam.commutes (ψ o)
  suffices key : ∀ (ψ' : Onr →ₐ[𝒪] L')
      (_ : (lam.restrictScalars 𝒪).comp ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) = ψ')
      (hψ'' : ψ' = (IsScalarTower.toAlgHom 𝒪 C L').comp ψ),
      ∃ (v v' : FakeEllipticCurve.WithFullLevel Λ N n L')
        (ς : FakeEllipticCurve.Rigidification r π A₀ ψ' v.1)
        (ς' : FakeEllipticCurve.Rigidification r π A₀ ψ' v'.1)
        (hς : ς.d = d) (hς' : ς'.d = d')
        (j₀ : v.1.A ≅ v'.1.A) (hj : j₀.hom ≫ v'.1.f = v.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia v v' j₀ hj)
        (_ : (∃ (ib : ς.Eb.A ⟶ ς'.Eb.A) (_ : ib ≫ ς'.gb = ς.gb ≫ j₀.hom) (_ : ib ≫ ς'.Eb.f = ς.Eb.f)
        (uA : ς'.Ab.A ⟶ ς.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ς.Ab ς'.Ab uA) (_ : uA ≫ ς.gA = ς'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ς'.φ ≫ uA ≫ ς.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ς.φ ≫ ς.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
        (ptX d L' ψ' hψ'' v ς hς h0').1 = Spec.map (CommRingCat.ofHom (lam : L →+* L')) ≫ (ptX d L _ rfl u ρ hd h0).1 ∧
          (ptX d' L' ψ' hψ'' v' ς' hς' h0').1 = Spec.map (CommRingCat.ofHom (lam : L →+* L')) ≫ (ptX d' L _ rfl u' ρ' hd' h0).1 by
    exact key _ hleg rfl
  intro ψ' hψ' hψ''
  subst hψ'

  obtain ⟨v, gv, hgv, hmulv, hactv, hlevv, -, hPv⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (lam : L →+* L') u
  have hpbv : FakeEllipticCurve.IsPullbackVia (lam : L →+* L') u.1 v.1 gv := ⟨hgv, hmulv, hactv, hlevv⟩
  obtain ⟨v', gv', hgv', hmulv', hactv', hlevv', -, hPv'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (lam : L →+* L') u'
  have hpbv' : FakeEllipticCurve.IsPullbackVia (lam : L →+* L') u'.1 v'.1 gv' := ⟨hgv', hmulv', hactv', hlevv'⟩

  obtain ⟨ς, hς⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀
    L L' (lam.restrictScalars 𝒪) ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1 v.1 gv hpbv ρ
  obtain ⟨ς', hς'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia 𝒪 π Onr Λ A₀
    L L' (lam.restrictScalars 𝒪) ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u'.1 v'.1 gv' hpbv' ρ'
  have hdς : ς.d = ρ.d := by obtain ⟨-, -, -, -, -, -, h, -⟩ := hς; exact h
  have hdς' : ς'.d = ρ'.d := by obtain ⟨-, -, -, -, -, -, h, -⟩ := hς'; exact h

  obtain ⟨hvm, hva, hvl, hvP⟩ := hvia
  obtain ⟨ib, hib, hibf, uA, huA, huAg, i₁, j₁, hc⟩ := hcorr
  obtain ⟨j₀, hj₀, hjvia, hjg, ibφ, hibφ, hibfφ, uAφ, huAφ, huAgφ, hcφ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isPullbackVia 𝒪 π Onr Λ hΛℤ A₀
      L L' (lam.restrictScalars 𝒪) ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1 u'.1 i₀ hi ⟨hvm, hva, hvl⟩
      ρ ρ' ib hib hibf uA huA huAg i₁ j₁ hc v.1 gv hpbv v'.1 gv' hpbv' ς hς ς' hς'

  have hPj : mapPt j₀.hom hj₀ v.2.P = v'.2.P := by
    apply Subtype.ext
    apply hgv'.hom_ext
    · show (v.2.P.1 ≫ j₀.hom) ≫ gv' = v'.2.P.1 ≫ gv'
      have e := congrArg Subtype.val hvP
      simp only [mapPt] at e
      rw [Category.assoc, hjg, ← Category.assoc, hPv, Category.assoc, e, hPv']
    · show (v.2.P.1 ≫ j₀.hom) ≫ v'.1.f = v'.2.P.1 ≫ v'.1.f
      rw [Category.assoc, hj₀, v.2.P.2, v'.2.P.2]
  obtain ⟨hjm, hja, hjl⟩ := hjvia

  have e1 := hx2 d L L' lam _ rfl hψ'' u v ρ ς gv hpbv hd (hdς.trans hd) h0 h0' hPv hς
  have e2 := hx2 d' L L' lam _ rfl hψ'' u' v' ρ' ς' gv' hpbv' hd' (hdς'.trans hd') h0 h0' hPv' hς'
  exact ⟨v, v', ς, ς', hdς.trans hd, hdς'.trans hd', j₀, hj₀, ⟨hjm, hja, hjl, hPj⟩,
    ⟨ibφ, hibφ, hibfφ, uAφ, huAφ, huAgφ, i₁, j₁, hcφ⟩, e1, e2⟩

theorem middle_glue
    {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)

    {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
    (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g))

    (hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
        (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
        (hd : ρ.d = d) (hd' : ρ'.d = d),
        ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 →
          ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
            ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
              ib ≫ ρ'.φ ≫ uA = ρ.φ)
    (L : Type) [CommRing L] [Algebra C L] [Algebra 𝒪 L] [IsScalarTower 𝒪 C L]
    (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
    (d d' d'' : ℕ)

    (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1)
    (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u'.1)
    (hd : ρ.d = d) (hd' : ρ'.d = d')
    (i₀ : u.1.A ≅ u'.1.A) (hi : i₀.hom ≫ u'.1.f = u.1.f) (hvia : FakeEllipticCurve.WithFullLevel.IsoVia u u' i₀ hi)
    (hcorr : (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i₀.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (v v' : FakeEllipticCurve.WithFullLevel Λ N n L)
    (ς : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v.1)
    (ς' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) v'.1)
    (hς : ς.d = d') (hς' : ς'.d = d'')
    (i₀' : v.1.A ≅ v'.1.A) (hi' : i₀'.hom ≫ v'.1.f = v.1.f) (hvia' : FakeEllipticCurve.WithFullLevel.IsoVia v v' i₀' hi')
    (hcorr' : (∃ (ib : ς.Eb.A ⟶ ς'.Eb.A) (_ : ib ≫ ς'.gb = ς.gb ≫ i₀'.hom) (_ : ib ≫ ς'.Eb.f = ς.Eb.f)
        (uA : ς'.Ab.A ⟶ ς.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ς.Ab ς'.Ab uA) (_ : uA ≫ ς.gA = ς'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ς'.φ ≫ uA ≫ ς.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ς.φ ≫ ς.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (hmid : (ptX d' L _ rfl u' ρ' hd' h0).1 = (ptX d' L _ rfl v ς hς h0).1) :
    ∃ (k₀ : u.1.A ≅ v'.1.A) (hk : k₀.hom ≫ v'.1.f = u.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia u v' k₀ hk),
      (∃ (ib : ρ.Eb.A ⟶ ς'.Eb.A) (_ : ib ≫ ς'.gb = ρ.gb ≫ k₀.hom) (_ : ib ≫ ς'.Eb.f = ρ.Eb.f)
        (uA : ς'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ς'.Ab uA) (_ : uA ≫ ρ.gA = ς'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ς'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by
  obtain ⟨ib₁, hib₁, hibf₁, uA₁, huA₁, huAg₁, i₁, j₁, h₁⟩ := hcorr
  obtain ⟨ib₃, hib₃, hibf₃, uA₃, huA₃, huAg₃, i₃, j₃, h₃⟩ := hcorr'
  obtain ⟨jm, hjm, hviam, ib₂, hib₂, hibf₂, uA₂, huA₂, huAg₂, h₂⟩ :=
    hx4 d' L _ rfl h0 u' v ρ' ς hd' hς (Subtype.ext hmid)
  have h₂' : ib₂ ≫ ς.φ ≫ uA₂ ≫ ρ'.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [← h₂]; simp only [Category.assoc]
  obtain ⟨ib₁₂, hib₁₂, hibf₁₂, uA₁₂, huA₁₂, huAg₁₂, i₁₂, j₁₂, h₁₂⟩ :=
    Ws47RL.corr_comp hΛℤ ρ ρ' ς i₀.hom jm.hom ib₁ hib₁ hibf₁ uA₁ huA₁ huAg₁ i₁ j₁ h₁ ib₂ hib₂ hibf₂ uA₂ huA₂ huAg₂ 0 0 h₂'
  obtain ⟨ib, hib, hibf, uA, huA, huAg, iF, jF, hF⟩ :=
    Ws47RL.corr_comp hΛℤ ρ ς ς' (i₀.hom ≫ jm.hom) i₀'.hom ib₁₂ hib₁₂ hibf₁₂ uA₁₂ huA₁₂ huAg₁₂ i₁₂ j₁₂ h₁₂
      ib₃ hib₃ hibf₃ uA₃ huA₃ huAg₃ i₃ j₃ h₃
  obtain ⟨hk₁, hvia₁₂⟩ := Ws47RL.isoVia_trans u u' v i₀ jm hi hjm hvia hviam
  obtain ⟨hk, hviaF⟩ := Ws47RL.isoVia_trans u v v' (i₀ ≪≫ jm) i₀' hk₁ hi' hvia₁₂ hvia'
  refine ⟨(i₀ ≪≫ jm) ≪≫ i₀', hk, hviaF, ib, ?_, hibf, uA, huA, huAg, iF, jF, hF⟩
  rw [hib]; simp only [Iso.trans_hom, Category.assoc]

end Ws47RL

namespace Ws47RL

section Engine

variable {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
  {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
  (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
    ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g))

def RelLocF (T : Type) [CommRing T] [Algebra C T] (d : ℕ)
    (x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d) (d' : ℕ)
    (x' : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d') : Prop :=
      ∃ (m : ℕ) (f : Fin m → (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})),
        Ideal.span (Set.range f) = ⊤ ∧
        ∀ k : Fin m,
          ∃ (L : Type) (_ : CommRing L) (_ : Algebra (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)
            (_ : IsLocalization.Away (f k) L) (_ : Algebra C L)
            (_ : IsScalarTower C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)
            (_ : Algebra 𝒪 L) (_ : IsScalarTower 𝒪 C L)
            (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
            (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1)
            (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u'.1)
            (hd : ρ.d = d) (hd' : ρ'.d = d')
            (i₀ : u.1.A ≅ u'.1.A) (hi : i₀.hom ≫ u'.1.f = u.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia u u' i₀ hi)
            (_ : (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i₀.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
                (i₁ j₁ : ℕ),
                ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
            (ptX d L _ rfl u ρ hd h0).1 =
                Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ x ∧
              (ptX d' L _ rfl u' ρ' hd' h0).1 =
                Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ x'

open CerednikDrinfeld.QM.FakeEllipticCurve in

theorem relLocF_refl
    (hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g)),
        ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
          ptX d T ψT hψT u ρ hd h0 = x)
    (T : Type) [CommRing T] [Algebra C T] (d : ℕ)
    (x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d)
    (hx : x ≫ ξ d ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})))) :
    RelLocF 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX T d x d x := by
  classical
  unfold RelLocF
  letI algO : Algebra 𝒪 (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) := ((algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})).comp (algebraMap 𝒪 C)).toAlgebra
  haveI hST : IsScalarTower 𝒪 C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h0 : algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (algebraMap 𝒪 C π) = 0 := by
    show Ideal.Quotient.mk _ (algebraMap C T (algebraMap 𝒪 C π)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  obtain ⟨u, ρ, hd, hpt⟩ := hx3 d (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) _ rfl h0 ⟨x, hx⟩
  have hAway : IsLocalization.Away (1 : (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  obtain ⟨hi, hvia⟩ := Ws47RL.isoVia_refl u
  have hpt1 : (ptX d (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) _ rfl u ρ hd h0).1 =
      Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ x := by
    rw [hpt, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨1, fun _ => 1, by simp, fun k => ⟨(T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}), inferInstance, Algebra.id _, hAway, inferInstance,
    IsScalarTower.right, algO, hST, h0, u, u, ρ, ρ, hd, hd, Iso.refl _, hi, hvia,
    ⟨𝟙 _, by simp, by simp, 𝟙 _, Ws47RL.isPullbackVia_id_self ρ.Ab, by simp, 0, 0, by simp⟩, hpt1, hpt1⟩⟩

theorem relLocF_symm
    [Fact r.Prime] (hrN : ¬ r ∣ N) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (T : Type) [CommRing T] [Algebra C T] (d d' : ℕ)
    (x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d)
    (x' : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d')
    (h : RelLocF 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX T d x d' x') :
    RelLocF 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX T d' x' d x := by
  unfold RelLocF at h ⊢
  obtain ⟨m, f, hf, hk⟩ := h
  refine ⟨m, f, hf, fun k => ?_⟩
  obtain ⟨L, iCR, iAlg, iAway, iC, iST, iO, iST', h0, u, u', ρ, ρ', hd, hd', i₀, hi, hvia,
    ⟨ib, hib, hibf, uA, huA, huAg, i₁, j₁, hcorr⟩, hx1, hx2⟩ := hk k
  have hπ : algebraMap 𝒪 L π = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪 C L π]; exact h0
  have hNB := Ws47RL.isUnit_natCast_quot_of_not_dvd (N := N) hrN hunr hπ
  obtain ⟨hi', hvia'⟩ := Ws47RL.isoVia_symm u u' i₀ hi hvia
  obtain ⟨ib', hib', hibf', uA', huA', huAg', i₂, j₂, hcorr'⟩ :=
    Ws47RL.exists_corr_symm hΛℤ hNB i₀ hi ρ ρ' ib hib hibf uA huA huAg i₁ j₁ hcorr
  exact ⟨L, iCR, iAlg, iAway, iC, iST, iO, iST', h0, u', u, ρ', ρ, hd', hd, i₀.symm, hi', hvia',
    ⟨ib', hib', hibf', uA', huA', huAg', i₂, j₂, hcorr'⟩, hx2, hx1⟩

theorem relLocF_trans

    (hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
        (gu : u'.1.A ⟶ u.1.A) (hgu : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 gu)
        (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
        (u'.2.P).1 ≫ gu = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) gu hgu ρ ρ' →
          (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
            Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)

    (hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
        (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
        (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
        (hd : ρ.d = d) (hd' : ρ'.d = d),
        ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 →
          ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
            ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
              ib ≫ ρ'.φ ≫ uA = ρ.φ)
    (T : Type) [CommRing T] [Algebra C T] (d d' d'' : ℕ)
    (x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d)
    (x' : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d')
    (x'' : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X d'')
    (h : RelLocF 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX T d x d' x')
    (h' : RelLocF 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX T d' x' d'' x'') :
    RelLocF 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX T d x d'' x'' := by
  classical
  unfold RelLocF at h h' ⊢
  obtain ⟨m, f, hf, hk⟩ := h
  obtain ⟨m', f', hf', hk'⟩ := h'
  refine ⟨m * m', fun j => f (finProdFinEquiv.symm j).1 * f' (finProdFinEquiv.symm j).2, ?_, fun j => ?_⟩
  ·
    apply top_le_iff.mp
    calc (⊤ : Ideal (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) = ⊤ * ⊤ := (Ideal.top_mul ⊤).symm
      _ = Ideal.span (Set.range f) * Ideal.span (Set.range f') := by rw [hf, hf']
      _ = Ideal.span (Set.range f * Set.range f') := Ideal.span_mul_span' _ _
      _ ≤ _ := by
        apply Ideal.span_mono
        rw [Set.mul_subset_iff]
        rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
        exact ⟨finProdFinEquiv (k, l), by simp⟩
  · set k := (finProdFinEquiv.symm j).1 with hk_def
    set l := (finProdFinEquiv.symm j).2 with hl_def
    obtain ⟨L, iCR, iAlg, iAway, iC, iST, iO, iST', h0, u, u', ρ, ρ', hd, hd', i₀, hi, hvia, hcorr, hx1, hx2e⟩ := hk k
    obtain ⟨L', iCR', iAlg', iAway', iC', iSTb', iO', iST'', h0', v, v', ς, ς', hς, hς', i₀', hi', hvia', hcorr', hy1, hy2⟩ := hk' l

    let L'' := Localization.Away (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L (f' l))
    have h0'' : algebraMap C L'' (algebraMap 𝒪 C π) = 0 := by
      rw [IsScalarTower.algebraMap_apply C L L'', h0, map_zero]

    let lam₁ : L →ₐ[C] L'' := IsScalarTower.toAlgHom C L L''
    have hlam₁ : (lam₁ : L →+* L'').comp (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L) = algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L'' := by
      rw [IsScalarTower.coe_toAlgHom, ← IsScalarTower.algebraMap_eq]
    let w₂ : L' →+* L'' := IsLocalization.Away.awayToAwayRight (S := L') (f' l) (f k) (P := L'')
    have hw₂ : w₂.comp (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L') = algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L'' :=
      RingHom.ext fun a => IsLocalization.Away.awayToAwayRight_eq (S := L') (f' l) (f k) (P := L'') a
    let lam₂ : L' →ₐ[C] L'' :=
      { toRingHom := w₂
        commutes' := fun c => by
          show w₂ (algebraMap C L' c) = algebraMap C L'' c
          rw [IsScalarTower.algebraMap_apply C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L' c, ← RingHom.comp_apply, hw₂,
            ← IsScalarTower.algebraMap_apply] }
    have hlam₂ : (lam₂ : L' →+* L'').comp (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L') = algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L'' := hw₂

    obtain ⟨v₁, v₁', ς₁, ς₁', hς₁, hς₁', j₁, hj₁, hvia₁, hcorr₁, he1, he1'⟩ :=
      Ws47RL.transport 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX hx2 L L'' lam₁ h0 h0'' d d' u u' ρ ρ' hd hd' i₀ hi hvia hcorr
    obtain ⟨w₁, w₁', τ₁, τ₁', hτ₁, hτ₁', j₂, hj₂, hvia₂, hcorr₂, he2, he2'⟩ :=
      Ws47RL.transport 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX hx2 L' L'' lam₂ h0' h0'' d' d'' v v' ς ς' hς hς' i₀' hi' hvia' hcorr'

    have hSpec : ∀ {R : Type} [CommRing R] (φ : R →+* L'') (χ : (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) →+* R),
        φ.comp χ = algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L'' →
        ∀ {e : ℕ} (y : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X e),
          Spec.map (CommRingCat.ofHom φ) ≫ (Spec.map (CommRingCat.ofHom χ) ≫ y) =
            Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L'')) ≫ y := by
      intro R _ φ χ hφ e y
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
    have hmid : (ptX d' L'' _ rfl v₁' ς₁' hς₁' h0'').1 = (ptX d' L'' _ rfl w₁ τ₁ hτ₁ h0'').1 := by
      rw [he1', he2, hx2e, hy1, hSpec _ _ hlam₁, hSpec _ _ hlam₂]
    obtain ⟨k₀, hk₀, hvia₃, hcorr₃⟩ :=
      Ws47RL.middle_glue 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ ptX hx4 L'' h0'' d d' d'' v₁ v₁' ς₁ ς₁' hς₁ hς₁' j₁ hj₁ hvia₁ hcorr₁
        w₁ w₁' τ₁ τ₁' hτ₁ hτ₁' j₂ hj₂ hvia₂ hcorr₂ hmid
    refine ⟨L'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      h0'', v₁, w₁', ς₁, τ₁', hς₁, hτ₁', k₀, hk₀, hvia₃, hcorr₃, ?_, ?_⟩
    · rw [he1, hx1, hSpec _ _ hlam₁]
    · rw [he2', hy2, hSpec _ _ hlam₂]

end Engine

end Ws47RL

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hx2 : (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1))

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hx4 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
                (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
                (hd : ρ.d = d) (hd' : ρ'.d = d),
                (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u' ρ' hd' h0 →
                  ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                    ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                      (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                      ib ≫ ρ'.φ ≫ uA = ρ.φ))
    (T : Type) [CommRing T] [Algebra C T] :
    Equivalence (RigidifiedPairClass.Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf T) := by
  refine ⟨fun p => ⟨rfl, ?_⟩, fun {p q} h => ⟨h.1.symm, ?_⟩, fun {p q s} h h' => ⟨h.1.trans h'.1, ?_⟩⟩
  · have hx : p.x ≫ ξ p.d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
        Spec.map (CommRingCat.ofHom (algebraMap C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) := by
      rw [← Category.assoc, p.hx, Category.assoc, p.ht, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact Ws47RL.relLocF_refl 𝒪 π Onr Λ hΛℤ A₀ n C ψ _ X ξ (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) hx3 T p.d p.x hx
  · exact Ws47RL.relLocF_symm 𝒪 π Onr Λ hΛℤ A₀ n C ψ _ X ξ (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) hrN hunr T p.d q.d p.x q.x h.2
  · exact Ws47RL.relLocF_trans 𝒪 π Onr Λ hΛℤ A₀ n C ψ _ X ξ (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) hx2 hx4 T p.d q.d s.d p.x q.x s.x h.2 h'.2

end S_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence
end P2MW
export P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_rel_equivalence (solution)
