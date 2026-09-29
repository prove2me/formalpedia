-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_forall_local_via
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6d4d4a56-ef46-506d-88bf-3703516639b1

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_forall_local_via
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace BodyL2

universe u

variable {a b : ℚ}

def RepresentsExtraLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {S : Type} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) {Z : Scheme.{0}} (ζ : Z ⟶ Spec (CommRingCat.of S))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
      FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ) :
    Prop :=
  (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (K K' : u'.1.ExtraLevel N),
            (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) → ptZ T φ u' hu' K = ptZ T φ u' hu' K') ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
            (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T) (u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T')
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (hu'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'')
            (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) (g : u''.1.A ⟶ u'.1.A),

            FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g →
            (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
            (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
              FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) →
              (ptZ T' (ψ.comp φ) u'' hu'' K'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ u' hu' K').1) ∧

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ), ∃ K : u'.1.ExtraLevel N, ptZ T φ u' hu' K = z) ∧
        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (K K' : u'.1.ExtraLevel N), ptZ T φ u' hu' K = ptZ T φ u' hu' K' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P)

section Glue

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
  {M₁ : Scheme.{0}} {π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)}
  {ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
    FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁}
  (hM₁ : IsFineModuli Λ 1 m M₁ π₁ ptF₁)

abbrev ringOf (U : M₁.affineOpens) : Type := Γ(M₁, U.1)

noncomputable def chartι (U : M₁.affineOpens) : Spec (CommRingCat.of (ringOf (M₁ := M₁) U)) ⟶ M₁ :=
  U.2.isoSpec.inv ≫ U.1.ι

noncomputable def chartBase (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)) (U : M₁.affineOpens) :
    Spec (CommRingCat.of (ringOf (M₁ := M₁) U)) ⟶ Spec (CommRingCat.of 𝒪) :=
  chartι U ≫ π₁

include hM₁ in

theorem exists_universal (U : M₁.affineOpens) :
    ∃ uU : FakeEllipticCurve.WithFullLevel Λ 1 m (ringOf (M₁ := M₁) U),
      (ptF₁ (ringOf U) (chartBase π₁ U) uU).1 = chartι U := by
  obtain ⟨uU, h⟩ := hM₁.ptF_surjective (ringOf U) (chartBase π₁ U) ⟨chartι U, rfl⟩
  exact ⟨uU, by rw [h]⟩

include hM₁ in

noncomputable def uof (U : M₁.affineOpens) : FakeEllipticCurve.WithFullLevel Λ 1 m (ringOf (M₁ := M₁) U) :=
  (exists_universal hM₁ U).choose

include hM₁ in
theorem ptF₁_uof (U : M₁.affineOpens) :
    (ptF₁ (ringOf U) (chartBase π₁ U) (uof hM₁ U)).1 = chartι U :=
  (exists_universal hM₁ U).choose_spec

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  obtain ⟨P, hP1⟩ := P; obtain ⟨P', hP1'⟩ := P'; obtain ⟨Q, hQ1⟩ := Q; obtain ⟨Q', hQ1'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ; rfl

theorem isPullback_of_iso_of_isPullback {N' : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N' m S) (v w : FakeEllipticCurve.WithFullLevel Λ N' m S')
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback φ u w) (hvw : FakeEllipticCurve.WithFullLevel.Iso v w) :
    FakeEllipticCurve.WithFullLevel.IsPullback φ u v := by
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := hw
  obtain ⟨e, he, emul, eact, elev, eP⟩ := hvw
  have sq1 : IsPullback e.hom v.1.f w.1.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  have sq : IsPullback (e.hom ≫ g) v.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)) := by
    simpa using sq1.paste_horiz hg
  refine ⟨e.hom ≫ g, sq, ?_, ?_, ?_, ?_⟩
  · intro T t' P Q
    have h1 := congrArg Subtype.val (emul t' P Q)
    simp only [mapPt_coe] at h1
    rw [← Category.assoc, h1, hmul t' (mapPt e.hom he P) (mapPt e.hom he Q)]
    exact mul_val_congr u.1.L rfl _ _ _ _ (by simp [Category.assoc]) (by simp [Category.assoc])
  · intro x
    rw [← Category.assoc, eact x, Category.assoc, hact x, Category.assoc]
  · intro T t' P hPlev
    obtain ⟨P₀, hP₀⟩ := hlev t' (mapPt e.hom he P) ((elev t' P).mp hPlev)
    exact ⟨P₀, by rw [hP₀, mapPt_coe, Category.assoc]⟩
  · rw [← Category.assoc, show (v.2.P).1 ≫ e.hom = (w.2.P).1 from congrArg Subtype.val eP, hP]

theorem isPullback_comp {N' : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'')
    (u : FakeEllipticCurve.WithFullLevel Λ N' m S) (u' : FakeEllipticCurve.WithFullLevel Λ N' m S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N' m S'')
    (h' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (h'' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'') :
    FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'' := by
  obtain ⟨g', hg', mul', act', lev', P'⟩ := h'
  obtain ⟨g'', hg'', mul'', act'', lev'', P''⟩ := h''
  have hSpec : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have sq : IsPullback (g'' ≫ g') u''.1.f u.1.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hSpec]; exact hg''.paste_horiz hg'
  refine ⟨g'' ≫ g', sq, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [← Category.assoc, mul'' t P Q, mul' (t ≫ Spec.map (CommRingCat.ofHom ψ))]
    exact mul_val_congr u.1.L (by rw [hSpec, Category.assoc]) _ _ _ _ (by simp [Category.assoc]) (by simp [Category.assoc])
  · intro x
    rw [← Category.assoc, act'' x, Category.assoc, act' x, Category.assoc]
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := lev'' t P hP
    obtain ⟨P₁, hP₁⟩ := lev' (t ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1 ≫ g'', by
      rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    exact ⟨P₁, by rw [hP₁, Category.assoc]⟩
  · rw [← Category.assoc, P'', Category.assoc, P', ← Category.assoc, ← hSpec]

noncomputable def resRing {U V : M₁.affineOpens} (hVU : V ≤ U) : ringOf U →+* ringOf V :=
  (M₁.presheaf.map (homOfLE hVU).op).hom

noncomputable def toRingOf (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)) (U : M₁.affineOpens) : 𝒪 →+* ringOf U :=
  (Spec.preimage (chartBase π₁ U)).hom

theorem chartBase_eq (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)) (U : M₁.affineOpens) :
    chartBase π₁ U = Spec.map (CommRingCat.ofHom (toRingOf π₁ U)) := by
  simp [toRingOf]

theorem spec_resRing_isoSpec {U V : M₁.affineOpens} (hVU : V ≤ U) :
    Spec.map (CommRingCat.ofHom (resRing hVU)) ≫ U.2.isoSpec.inv = V.2.isoSpec.inv ≫ M₁.homOfLE hVU := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  simp only [resRing, CommRingCat.ofHom_hom]
  exact IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE hVU).op

theorem spec_resRing_comp_chartι {U V : M₁.affineOpens} (hVU : V ≤ U) :
    Spec.map (CommRingCat.ofHom (resRing hVU)) ≫ chartι U = chartι V := by
  simp only [chartι]
  rw [← Category.assoc, spec_resRing_isoSpec hVU, Category.assoc, Scheme.homOfLE_ι]

include hM₁ in

theorem uof_isPullback {U V : M₁.affineOpens} (hVU : V ≤ U) :
    FakeEllipticCurve.WithFullLevel.IsPullback (resRing hVU) (uof hM₁ U) (uof hM₁ V) := by
  obtain ⟨w, hw⟩ := FakeEllipticCurve.WithFullLevel.exists_isPullback (resRing hVU) (uof hM₁ U)
  have hbase : Spec.map (CommRingCat.ofHom (resRing hVU)) ≫ chartBase π₁ U = chartBase π₁ V := by
    simp only [chartBase]; rw [← Category.assoc, spec_resRing_comp_chartι]
  have h1 := hM₁.ptF_pullback _ _ (resRing hVU) (chartBase π₁ U) (chartBase π₁ V) hbase (uof hM₁ U) w hw
  rw [ptF₁_uof hM₁ U, spec_resRing_comp_chartι, ← ptF₁_uof hM₁ V] at h1
  have h2 : ptF₁ _ (chartBase π₁ V) (uof hM₁ V) = ptF₁ _ (chartBase π₁ V) w := Subtype.ext h1.symm
  exact isPullback_of_iso_of_isPullback _ _ _ _ hw (hM₁.ptF_injective _ _ _ _ h2)

variable (N) (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
  (hloc : ∀ (S : Type) [CommRing S], IsUnit ((N : ℕ) : S) → IsUnit ((m : ℕ) : S) →
    ∀ u : FakeEllipticCurve.WithFullLevel Λ 1 m S,
      ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
        (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N →
            SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        RepresentsExtraLevel Λ N m u ζ ptZ)

theorem isUnit_N_ringOf (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)) (hN : IsUnit ((N : ℕ) : 𝒪)) (U : M₁.affineOpens) :
    IsUnit ((N : ℕ) : ringOf (M₁ := M₁) U) := by
  simpa using hN.map (toRingOf π₁ U)

theorem isUnit_m_ringOf (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪)) (U : M₁.affineOpens) :
    IsUnit ((m : ℕ) : ringOf (M₁ := M₁) U) := by
  simpa using hm'.map (toRingOf π₁ U)

structure LocalDatum (U : M₁.affineOpens) (u : FakeEllipticCurve.WithFullLevel Λ 1 m (ringOf U)) where
  Z : Scheme.{0}
  ζ : Z ⟶ Spec (CommRingCat.of (ringOf U))
  finite : IsFinite ζ
  etale : Etale ζ
  ptZ : ∀ (T : Type) [CommRing T] (φ : ringOf U →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ
  represents : RepresentsExtraLevel Λ N m u ζ ptZ

theorem LocalDatum.ptZ_congr {U : M₁.affineOpens} {u : FakeEllipticCurve.WithFullLevel Λ 1 m (ringOf U)}
    (D : LocalDatum N U u) {T : Type} [CommRing T] {φ₁ φ₂ : ringOf U →+* T} (h : φ₁ = φ₂)
    (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
    (h₁ : FakeEllipticCurve.WithFullLevel.IsPullback φ₁ u u') (h₂ : FakeEllipticCurve.WithFullLevel.IsPullback φ₂ u u')
    (K : u'.1.ExtraLevel N) : (D.ptZ T φ₁ u' h₁ K).1 = (D.ptZ T φ₂ u' h₂ K).1 := by
  subst h; rfl

theorem presheaf_map_hom_eq_id {U : M₁.Opens} (φ : U ⟶ U) : (M₁.presheaf.map φ.op).hom = RingHom.id _ := by
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
  rw [op_id, M₁.presheaf.map_id]; rfl

theorem presheaf_map_hom_comp {U V W : M₁.Opens} (φ : W ⟶ V) (ψ : V ⟶ U) (χ : W ⟶ U) :
    (M₁.presheaf.map φ.op).hom.comp (M₁.presheaf.map ψ.op).hom = (M₁.presheaf.map χ.op).hom := by
  obtain rfl : χ = φ ≫ ψ := Subsingleton.elim _ _
  rw [op_comp, M₁.presheaf.map_comp]; rfl

theorem resRing_refl (U : M₁.affineOpens) : resRing (le_refl U) = RingHom.id (ringOf U) :=
  presheaf_map_hom_eq_id _

theorem resRing_comp {U V W : M₁.affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    (resRing hWV).comp (resRing hVU) = resRing (hWV.trans hVU) :=
  presheaf_map_hom_comp _ _ _

include π₁ hN hm' hloc in
theorem nonempty_localDatum (U : M₁.affineOpens) (u : FakeEllipticCurve.WithFullLevel Λ 1 m (ringOf U)) :
    Nonempty (LocalDatum N U u) := by
  obtain ⟨Z, ζ, hf, he, ptZ, h⟩ := hloc (ringOf U) (isUnit_N_ringOf N π₁ hN U) (isUnit_m_ringOf π₁ hm' U) u
  exact ⟨⟨Z, ζ, hf, he, ptZ, h⟩⟩

include hM₁ hN hm' hloc in

noncomputable def datum (U : M₁.affineOpens) : LocalDatum N U (uof hM₁ U) :=
  (nonempty_localDatum N (π₁ := π₁) hN hm' hloc U (uof hM₁ U)).some

include hM₁ hN hm' hloc in

theorem existsUnique_trans {U V : M₁.affineOpens} (hVU : V ≤ U) :
    ∃! e : (datum N hM₁ hN hm' hloc V).Z ⟶ (datum N hM₁ hN hm' hloc U).Z,
      CategoryTheory.IsPullback e (datum N hM₁ hN hm' hloc V).ζ (datum N hM₁ hN hm' hloc U).ζ
          (Spec.map (CommRingCat.ofHom (resRing hVU))) ∧
      ∀ (T : Type) [CommRing T] (ψ : ringOf V →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
        (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ (uof hM₁ V) u')
        (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp (resRing hVU)) (uof hM₁ U) u') (K : u'.1.ExtraLevel N),
        ((datum N hM₁ hN hm' hloc V).ptZ T ψ u' hu' K).1 ≫ e =
          ((datum N hM₁ hN hm' hloc U).ptZ T (ψ.comp (resRing hVU)) u' hu K).1 :=
  CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.existsUnique_hom_isPullback_of_represents_extraLevel Λ N m
    (uof hM₁ U) _ _ (datum N hM₁ hN hm' hloc U).represents (resRing hVU) (uof hM₁ V)
    (uof_isPullback hM₁ hVU) _ _ (datum N hM₁ hN hm' hloc V).represents

include hM₁ hN hm' hloc in

noncomputable def transZ {U V : M₁.affineOpens} (hVU : V ≤ U) :
    (datum N hM₁ hN hm' hloc V).Z ⟶ (datum N hM₁ hN hm' hloc U).Z :=
  (existsUnique_trans N hM₁ hN hm' hloc hVU).exists.choose

include hM₁ hN hm' hloc in
theorem transZ_spec {U V : M₁.affineOpens} (hVU : V ≤ U) :
    CategoryTheory.IsPullback (transZ N hM₁ hN hm' hloc hVU) (datum N hM₁ hN hm' hloc V).ζ (datum N hM₁ hN hm' hloc U).ζ
          (Spec.map (CommRingCat.ofHom (resRing hVU))) ∧
      ∀ (T : Type) [CommRing T] (ψ : ringOf V →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
        (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ (uof hM₁ V) u')
        (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp (resRing hVU)) (uof hM₁ U) u') (K : u'.1.ExtraLevel N),
        ((datum N hM₁ hN hm' hloc V).ptZ T ψ u' hu' K).1 ≫ transZ N hM₁ hN hm' hloc hVU =
          ((datum N hM₁ hN hm' hloc U).ptZ T (ψ.comp (resRing hVU)) u' hu K).1 :=
  (existsUnique_trans N hM₁ hN hm' hloc hVU).exists.choose_spec

include hM₁ hN hm' hloc in
theorem transZ_id (U : M₁.affineOpens) : transZ N hM₁ hN hm' hloc (le_refl U) = 𝟙 _ := by
  refine ((existsUnique_trans N hM₁ hN hm' hloc (le_refl U)).unique (transZ_spec N hM₁ hN hm' hloc (le_refl U)) ⟨?_, ?_⟩)
  · have h : Spec.map (CommRingCat.ofHom (resRing (le_refl U))) = 𝟙 _ := by
      rw [resRing_refl]; exact Spec.map_id _
    rw [h]
    exact CategoryTheory.IsPullback.of_horiz_isIso ⟨by simp⟩
  · intro T _ ψ u' hu' hu K
    rw [Category.comp_id]
    exact (datum N hM₁ hN hm' hloc U).ptZ_congr N (by rw [resRing_refl]; rfl) u' hu' hu K

include hM₁ hN hm' hloc in
theorem transZ_comp {U V W : M₁.affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    transZ N hM₁ hN hm' hloc hWV ≫ transZ N hM₁ hN hm' hloc hVU = transZ N hM₁ hN hm' hloc (hWV.trans hVU) := by
  refine (existsUnique_trans N hM₁ hN hm' hloc (hWV.trans hVU)).unique ⟨?_, ?_⟩
    (transZ_spec N hM₁ hN hm' hloc (hWV.trans hVU))
  · have p := (transZ_spec N hM₁ hN hm' hloc hWV).1.paste_horiz (transZ_spec N hM₁ hN hm' hloc hVU).1
    have h : Spec.map (CommRingCat.ofHom (resRing hWV)) ≫ Spec.map (CommRingCat.ofHom (resRing hVU)) =
        Spec.map (CommRingCat.ofHom (resRing (hWV.trans hVU))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, resRing_comp]
    rwa [h] at p
  · intro T _ ψ u' hu' hu K
    have hu₂ : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp (resRing hWV)) (uof hM₁ V) u' :=
      isPullback_comp _ _ _ _ _ (uof_isPullback hM₁ hWV) hu'
    have hu₃ : FakeEllipticCurve.WithFullLevel.IsPullback ((ψ.comp (resRing hWV)).comp (resRing hVU)) (uof hM₁ U) u' :=
      isPullback_comp _ _ _ _ _ (uof_isPullback hM₁ hVU) hu₂
    rw [← Category.assoc, (transZ_spec N hM₁ hN hm' hloc hWV).2 T ψ u' hu' hu₂ K,
      (transZ_spec N hM₁ hN hm' hloc hVU).2 T _ u' hu₂ hu₃ K]
    exact (datum N hM₁ hN hm' hloc U).ptZ_congr N (by rw [RingHom.comp_assoc, resRing_comp]) u' hu₃ hu K

include hM₁ hN hm' hloc in

noncomputable def gluingData : Scheme.Cover.RelativeGluingData M₁.directedAffineCover where
  functor :=
    { obj := fun U => (datum N hM₁ hN hm' hloc U).Z
      map := fun {V U} f => transZ N hM₁ hN hm' hloc (leOfHom f)
      map_id := fun U => transZ_id N hM₁ hN hm' hloc U
      map_comp := fun {W V U} f g => (transZ_comp N hM₁ hN hm' hloc (leOfHom f) (leOfHom g)).symm }
  natTrans :=
    { app := fun U => (datum N hM₁ hN hm' hloc U).ζ ≫ U.2.isoSpec.inv
      naturality := by
        intro V U f
        simp only [Scheme.Cover.functorOfLocallyDirected_obj, Scheme.Cover.functorOfLocallyDirected_map]
        rw [← Category.assoc, (transZ_spec N hM₁ hN hm' hloc (leOfHom f)).1.w, Category.assoc, Category.assoc]
        congr 1
        exact spec_resRing_isoSpec (leOfHom f) }
  equifibered := by
    intro V U f
    simp only [Scheme.Cover.functorOfLocallyDirected_map]
    have sq : IsPullback (Spec.map (CommRingCat.ofHom (resRing (leOfHom f)))) V.2.isoSpec.inv U.2.isoSpec.inv
        (M₁.homOfLE (leOfHom f)) :=
      IsPullback.of_vert_isIso ⟨spec_resRing_isoSpec (leOfHom f)⟩
    exact (transZ_spec N hM₁ hN hm' hloc (leOfHom f)).1.paste_vert sq

include hM₁ hN hm' hloc in

noncomputable abbrev M : Scheme.{0} := (gluingData N hM₁ hN hm' hloc).glued

include hM₁ hN hm' hloc in

noncomputable abbrev fM : M N hM₁ hN hm' hloc ⟶ M₁ := (gluingData N hM₁ hN hm' hloc).toBase

include hM₁ hN hm' hloc in

theorem fM_of_forall (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : M₁.affineOpens, P (datum N hM₁ hN hm' hloc U).ζ) : P (fM N hM₁ hN hm' hloc) := by
  apply IsZariskiLocalAtTarget.of_openCover M₁.directedAffineCover
  intro U
  have sq := ((gluingData N hM₁ hN hm' hloc).isPullback_natTrans_ι_toBase U).flip
  have e : sq.isoPullback.hom ≫ pullback.snd _ _ = (gluingData N hM₁ hN hm' hloc).natTrans.app U :=
    sq.isoPullback_hom_snd
  have hP : P ((gluingData N hM₁ hN hm' hloc).natTrans.app U) := by
    change P ((datum N hM₁ hN hm' hloc U).ζ ≫ U.2.isoSpec.inv)
    exact (P.cancel_right_of_respectsIso _ _).mpr (h U)
  rw [← e] at hP
  exact (P.cancel_left_of_respectsIso _ _).mp hP

include hM₁ hN hm' hloc in
theorem isFinite_fM : IsFinite (fM N hM₁ hN hm' hloc) :=
  fM_of_forall N hM₁ hN hm' hloc @IsFinite fun U => (datum N hM₁ hN hm' hloc U).finite

include hM₁ hN hm' hloc in
theorem etale_fM : Etale (fM N hM₁ hN hm' hloc) :=
  fM_of_forall N hM₁ hN hm' hloc @Etale fun U => (datum N hM₁ hN hm' hloc U).etale

section Sec

variable {S : Type} [CommRing S] (t₁ : Spec (CommRingCat.of S) ⟶ M₁)

def SecIdx : Type :=
  {p : (Spec (CommRingCat.of S)).affineOpens × M₁.affineOpens // (p.1 : (Spec (CommRingCat.of S)).Opens) ≤ t₁ ⁻¹ᵁ p.2}

noncomputable scoped instance : Preorder (SecIdx t₁) := Preorder.lift fun p => p.1

theorem exists_secIdx (x : ↥(Spec (CommRingCat.of S))) (O : (Spec (CommRingCat.of S)).Opens) (hx : x ∈ O)
    (O₁ : M₁.Opens) (hx₁ : t₁ x ∈ O₁) :
    ∃ p : SecIdx t₁, x ∈ (p.1.1 : (Spec (CommRingCat.of S)).Opens) ∧ (p.1.1 : (Spec (CommRingCat.of S)).Opens) ≤ O ∧
      (p.1.2 : M₁.Opens) ≤ O₁ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := M₁.isBasis_affineOpens.exists_subset_of_mem_open hx₁ O₁.2
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := (Spec (CommRingCat.of S)).isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((t₁ ⁻¹ᵁ U) ⊓ O : (Spec (CommRingCat.of S)).Opens) from ⟨hxU, hx⟩) ((t₁ ⁻¹ᵁ U) ⊓ O).2
  exact ⟨⟨(⟨W, hW⟩, ⟨U, hU⟩), fun y hy => (hWO hy).1⟩, hxW, fun y hy => (hWO hy).2, hUO⟩

noncomputable def secCover : (Spec (CommRingCat.of S)).OpenCover :=
  Scheme.Cover.mkOfCovers (SecIdx t₁) (fun p => p.1.1) (fun p => (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι)
    (fun x => by
      obtain ⟨p, hx, -⟩ := exists_secIdx t₁ x ⊤ trivial ⊤ trivial
      exact ⟨p, ⟨x, hx⟩, rfl⟩)

noncomputable scoped instance : Preorder (secCover t₁).I₀ := inferInstanceAs (Preorder (SecIdx t₁))

noncomputable scoped instance : Scheme.Cover.LocallyDirected (secCover t₁) where
  trans {p q} hpq := (Spec (CommRingCat.of S)).homOfLE (show (p.1.1 : (Spec (CommRingCat.of S)).Opens) ≤ q.1.1 from (leOfHom hpq).1)
  trans_id p := by simp [secCover]; rfl
  trans_comp hpq hqr := by simp [secCover, Scheme.homOfLE_homOfLE]; exact (Scheme.homOfLE_homOfLE _ _ _).symm
  w hpq := by simp [secCover]; exact Scheme.homOfLE_ι _ _
  property_trans {p q} hpq :=
    (inferInstance : IsOpenImmersion ((Spec (CommRingCat.of S)).homOfLE (show (p.1.1 : (Spec (CommRingCat.of S)).Opens) ≤ q.1.1 from (leOfHom hpq).1)))
  directed {p q} x := by
    let y : ↥(Spec (CommRingCat.of S)) := (pullback.fst ((secCover t₁).f p) ((secCover t₁).f q) ≫ (secCover t₁).f p) x
    have hyp : y ∈ (p.1.1 : (Spec (CommRingCat.of S)).Opens) := by
      simp only [y, Scheme.Hom.comp_apply]
      exact ((pullback.fst ((secCover t₁).f p) ((secCover t₁).f q)) x).2
    have hyq : y ∈ (q.1.1 : (Spec (CommRingCat.of S)).Opens) := by
      have : y = (pullback.snd ((secCover t₁).f p) ((secCover t₁).f q) ≫ (secCover t₁).f q) x := by
        simp only [y, pullback.condition]
      rw [this, Scheme.Hom.comp_apply]
      exact ((pullback.snd ((secCover t₁).f p) ((secCover t₁).f q)) x).2
    obtain ⟨k, hyk, hkW, hkU⟩ := exists_secIdx t₁ y ((p.1.1 : (Spec (CommRingCat.of S)).Opens) ⊓ q.1.1) ⟨hyp, hyq⟩
      ((p.1.2 : M₁.Opens) ⊓ q.1.2) ⟨p.2 hyp, q.2 hyq⟩
    refine ⟨k, homOfLE ⟨fun z hz => (hkW hz).1, fun z hz => (hkU hz).1⟩,
      homOfLE ⟨fun z hz => (hkW hz).2, fun z hz => (hkU hz).2⟩, ⟨y, hyk⟩, ?_⟩
    apply (pullback.fst ((secCover t₁).f p) ((secCover t₁).f q) ≫ (secCover t₁).f p).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change ((Spec (CommRingCat.of S)).homOfLE _ ≫ (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ⟨y, hyk⟩ = y
    rw [Scheme.homOfLE_ι]
    rfl

abbrev Wring (p : SecIdx t₁) : Type := Γ(Spec (CommRingCat.of S), (p.1.1 : (Spec (CommRingCat.of S)).Opens))

noncomputable def Wι (p : SecIdx t₁) : Spec (CommRingCat.of (Wring t₁ p)) ⟶ Spec (CommRingCat.of S) :=
  p.1.1.2.isoSpec.inv ≫ (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι

noncomputable def rW (p : SecIdx t₁) : S →+* Wring t₁ p := (Spec.preimage (Wι t₁ p)).hom

theorem spec_rW (p : SecIdx t₁) : Spec.map (CommRingCat.ofHom (rW t₁ p)) = Wι t₁ p := by
  simp [rW]

scoped instance (p : SecIdx t₁) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (rW t₁ p))) := by
  rw [spec_rW]; unfold Wι; infer_instance

noncomputable def cmap (p : SecIdx t₁) :
    (p.1.1 : (Spec (CommRingCat.of S)).Opens).toScheme ⟶ (p.1.2 : M₁.Opens).toScheme :=
  t₁.resLE (p.1.2 : M₁.Opens) (p.1.1 : (Spec (CommRingCat.of S)).Opens) p.2

noncomputable def φW (p : SecIdx t₁) : ringOf p.1.2 →+* Wring t₁ p :=
  (Spec.preimage (p.1.1.2.isoSpec.inv ≫ cmap t₁ p ≫ p.1.2.2.isoSpec.hom)).hom

theorem spec_φW (p : SecIdx t₁) :
    Spec.map (CommRingCat.ofHom (φW t₁ p)) = p.1.1.2.isoSpec.inv ≫ cmap t₁ p ≫ p.1.2.2.isoSpec.hom := by
  simp [φW]

theorem spec_φW_chartι (p : SecIdx t₁) : Spec.map (CommRingCat.ofHom (φW t₁ p)) ≫ chartι p.1.2 = Wι t₁ p ≫ t₁ := by
  rw [spec_φW]; simp only [chartι, Wι, cmap, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

variable (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))

include hM₁ in

theorem isPullback_uof_of_ptF₁_eq (U : M₁.affineOpens) {T : Type} [CommRing T] (ψ : ringOf U →+* T)
    (s' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of 𝒪)) (hs' : Spec.map (CommRingCat.ofHom ψ) ≫ chartBase π₁ U = s')
    (v : FakeEllipticCurve.WithFullLevel Λ 1 m T) (hv : (ptF₁ T s' v).1 = Spec.map (CommRingCat.ofHom ψ) ≫ chartι U) :
    FakeEllipticCurve.WithFullLevel.IsPullback ψ (uof hM₁ U) v := by
  obtain ⟨w, hw⟩ := FakeEllipticCurve.WithFullLevel.exists_isPullback ψ (uof hM₁ U)
  have h1 := hM₁.ptF_pullback _ _ ψ (chartBase π₁ U) s' hs' (uof hM₁ U) w hw
  rw [ptF₁_uof hM₁ U, ← hv] at h1
  exact isPullback_of_iso_of_isPullback _ _ _ _ hw (hM₁.ptF_injective _ _ _ _ (Subtype.ext h1.symm))

omit hM₁ in
theorem ringHom_eq_of_spec_map_eq {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

omit hM₁ in

theorem spec_res_isoSpec_inv (X : Scheme.{0}) {U V : X.affineOpens} (h : V ≤ U) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.2.isoSpec.inv = V.2.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op

omit hM₁ in

theorem homOfLE_isoSpec (X : Scheme.{0}) {U V : X.affineOpens} (h : V ≤ U) :
    X.homOfLE h ≫ U.2.isoSpec.hom = V.2.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE h).op) := by
  have key := spec_res_isoSpec_inv X h
  calc X.homOfLE h ≫ U.2.isoSpec.hom = V.2.isoSpec.hom ≫ (V.2.isoSpec.inv ≫ X.homOfLE h) ≫ U.2.isoSpec.hom := by
        simp
    _ = V.2.isoSpec.hom ≫ (Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.2.isoSpec.inv) ≫ U.2.isoSpec.hom := by
        rw [key]
    _ = V.2.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE h).op) := by simp

noncomputable def ρW {p q : SecIdx t₁} (h : p ≤ q) : Wring t₁ q →+* Wring t₁ p :=
  ((Spec (CommRingCat.of S)).presheaf.map (homOfLE h.1).op).hom

theorem homOfLE_isoSpec_W {p q : SecIdx t₁} (h : p ≤ q) :
    (Spec (CommRingCat.of S)).homOfLE h.1 ≫ q.1.1.2.isoSpec.hom =
      p.1.1.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ρW _ h)) := by
  rw [homOfLE_isoSpec]; rfl

theorem spec_ρW {p q : SecIdx t₁} (h : p ≤ q) :
    Spec.map (CommRingCat.ofHom (ρW _ h)) ≫ q.1.1.2.isoSpec.inv =
      p.1.1.2.isoSpec.inv ≫ (Spec (CommRingCat.of S)).homOfLE h.1 :=
  spec_res_isoSpec_inv (Spec (CommRingCat.of S)) h.1

theorem ρW_comp_rW {p q : SecIdx t₁} (h : p ≤ q) : (ρW _ h).comp (rW t₁ q) = rW t₁ p := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_rW, spec_rW, Wι, Wι, ← Category.assoc, spec_ρW, Category.assoc,
    Scheme.homOfLE_ι]

theorem ρW_comp_φW {p q : SecIdx t₁} (h : p ≤ q) :
    (ρW _ h).comp (φW t₁ q) = (φW t₁ p).comp (resRing h.2) := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, spec_φW, spec_φW]

  rw [← Category.assoc (Spec.map _), spec_ρW]
  simp only [Category.assoc]
  congr 1

  have hU : p.1.2.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (resRing h.2)) = M₁.homOfLE h.2 ≫ q.1.2.2.isoSpec.hom := by
    rw [show CommRingCat.ofHom (resRing h.2) = M₁.presheaf.map (homOfLE h.2).op from rfl, homOfLE_isoSpec]
  rw [hU, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (q.1.2 : M₁.Opens).ι]
  simp only [cmap, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

section Pieces

variable (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)

noncomputable def uW (p : SecIdx t₁) : FakeEllipticCurve.WithFullLevel Λ 1 m (Wring t₁ p) :=
  (FakeEllipticCurve.WithFullLevel.exists_isPullback (rW t₁ p) u).choose

theorem uW_spec (p : SecIdx t₁) : FakeEllipticCurve.WithFullLevel.IsPullback (rW t₁ p) u (uW t₁ u p) :=
  (FakeEllipticCurve.WithFullLevel.exists_isPullback (rW t₁ p) u).choose_spec

noncomputable def gW (p : SecIdx t₁) : (uW t₁ u p).1.A ⟶ u.1.A := (uW_spec t₁ u p).choose

theorem gW_via (p : SecIdx t₁) :
    FakeEllipticCurve.IsPullbackVia (rW t₁ p) u.1 (uW t₁ u p).1 (gW t₁ u p) ∧
      ((uW t₁ u p).2.P).1 ≫ gW t₁ u p = Spec.map (CommRingCat.ofHom (rW t₁ p)) ≫ (u.2.P).1 := by
  obtain ⟨hg, hmul, hact, hlev, hP⟩ := (uW_spec t₁ u p).choose_spec
  exact ⟨⟨hg, hmul, hact, hlev⟩, hP⟩

noncomputable def KW (K : u.1.ExtraLevel N) (p : SecIdx t₁) : (uW t₁ u p).1.ExtraLevel N :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia (rW t₁ p) u.1
    (uW t₁ u p).1 (gW t₁ u p) (gW_via t₁ u p).1 N K).choose

theorem KW_spec (K : u.1.ExtraLevel N) (p : SecIdx t₁) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Wring t₁ p)))
    (P : SchemeHomOver t' (uW t₁ u p).1.f) :
    FactorsThrough (KW N t₁ u K p).levK P ↔
      FactorsThrough K.levK (t := t' ≫ Spec.map (CommRingCat.ofHom (rW t₁ p)))
        ⟨P.1 ≫ gW t₁ u p, by rw [Category.assoc, (gW_via t₁ u p).1.1.w, ← Category.assoc, P.2]⟩ :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia (rW t₁ p) u.1
    (uW t₁ u p).1 (gW t₁ u p) (gW_via t₁ u p).1 N K).choose_spec t' P

omit hM₁ in

theorem lev1_iff {T₀ : Type} [CommRing T₀] (E : FakeEllipticCurve Λ 1 T₀) {X : Scheme.{0}}
    (t : X ⟶ Spec (CommRingCat.of T₀)) (P : SchemeHomOver t E.f) : FactorsThrough E.lev P ↔ P = E.L.one t :=
  CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_eq_one_of_level_one E t P

omit hM₁ in

theorem one_comp_of_mul {N₁ N₂ : ℕ} {T T' : Type} [CommRing T] [CommRing T'] (φ : T →+* T')
    (E : FakeEllipticCurve Λ N₁ T) (E' : FakeEllipticCurve Λ N₂ T') (g : E'.A ⟶ E.A)
    (hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T')) (P Q : SchemeHomOver t E'.f),
      (E'.L.mul t P Q).1 ≫ g =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T')) :
    (E'.L.one t).1 ≫ g = (E.L.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  set y : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
    ⟨(E'.L.one t).1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, (E'.L.one t).2]⟩ with hy
  have hyy : E.L.mul _ y y = y := by
    apply Subtype.ext
    have := hmul t (E'.L.one t) (E'.L.one t)
    rw [E'.L.one_mul] at this
    exact this.symm
  have : y = E.L.one _ := by
    calc y = E.L.mul _ (E.L.one _) y := (E.L.one_mul _ y).symm
      _ = E.L.mul _ (E.L.mul _ (E.L.inv _ y) y) y := by rw [E.L.inv_mul_cancel]
      _ = E.L.mul _ (E.L.inv _ y) (E.L.mul _ y y) := E.L.mul_assoc _ _ _ _
      _ = E.L.mul _ (E.L.inv _ y) y := by rw [hyy]
      _ = E.L.one _ := E.L.inv_mul_cancel _ y
  exact congrArg Subtype.val this

omit hM₁ in

theorem hlev'_level_one {T T' : Type} [CommRing T] [CommRing T'] (φ : T →+* T')
    (E : FakeEllipticCurve Λ 1 T) (E' : FakeEllipticCurve Λ 1 T') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) :
    ∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t' E'.f),
      (∃ P₀ : X ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g) → FactorsThrough E'.lev P := by
  intro X t' P hP
  obtain ⟨hsq, hmul, -, -⟩ := hg
  rw [lev1_iff]
  have h1 : FactorsThrough E.lev (t := t' ≫ Spec.map (CommRingCat.ofHom φ))
      ⟨P.1 ≫ g, by rw [Category.assoc, hsq.w, ← Category.assoc, P.2]⟩ := hP
  rw [lev1_iff] at h1
  have h2 := congrArg Subtype.val h1
  rw [← one_comp_of_mul φ E E' g hsq hmul t'] at h2
  apply Subtype.ext
  apply hsq.hom_ext
  · exact h2
  · rw [P.2, (E'.L.one t').2]

theorem exists_gpq {p q : SecIdx t₁} (h : p ≤ q) :
    ∃ g : (uW t₁ u p).1.A ⟶ (uW t₁ u q).1.A,
      g ≫ gW t₁ u q = gW t₁ u p ∧
      FakeEllipticCurve.IsPullbackVia (ρW _ h) (uW t₁ u q).1 (uW t₁ u p).1 g ∧
      ((uW t₁ u p).2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (ρW _ h)) ≫ ((uW t₁ u q).2.P).1 := by
  obtain ⟨g, hcomp, hf, -, hvia⟩ :=
    FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq (rW t₁ q) (ρW _ h) (rW t₁ p)
      (ρW_comp_rW t₁ h) u.1 (uW t₁ u q).1 (uW t₁ u p).1 (gW t₁ u q) (gW_via t₁ u q).1
      (hlev'_level_one (rW t₁ q) u.1 (uW t₁ u q).1 (gW t₁ u q) (gW_via t₁ u q).1) (gW t₁ u p) (gW_via t₁ u p).1
  refine ⟨g, hcomp, hvia, ?_⟩
  apply (gW_via t₁ u q).1.1.hom_ext
  · rw [Category.assoc, hcomp, (gW_via t₁ u p).2, Category.assoc, (gW_via t₁ u q).2, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ρW_comp_rW]
  · rw [Category.assoc, hf, ← Category.assoc, ((uW t₁ u p).2.P).2, Category.assoc, ((uW t₁ u q).2.P).2]
    simp

include hM₁ in

theorem uW_isPullback_uof (ht₁ : (ptF₁ S s u).1 = t₁) (p : SecIdx t₁) :
    FakeEllipticCurve.WithFullLevel.IsPullback (φW t₁ p) (uof hM₁ p.1.2) (uW t₁ u p) := by
  have hs' : Spec.map (CommRingCat.ofHom (rW t₁ p)) ≫ s =
      Spec.map (CommRingCat.ofHom (φW t₁ p)) ≫ chartBase π₁ p.1.2 := by
    have hs : t₁ ≫ π₁ = s := by rw [← ht₁]; exact (ptF₁ S s u).2
    rw [show chartBase π₁ p.1.2 = chartι p.1.2 ≫ π₁ from rfl, ← Category.assoc, spec_φW_chartι, Category.assoc,
      hs, spec_rW]
  have h := hM₁.ptF_pullback _ _ (rW t₁ p) s _ hs' u (uW t₁ u p) (uW_spec t₁ u p)
  apply isPullback_uof_of_ptF₁_eq hM₁ p.1.2 (φW t₁ p) _ rfl (uW t₁ u p)
  rw [h, spec_rW, ht₁, ← spec_φW_chartι]

include hM₁ hN hm' hloc in

noncomputable def piece (ht₁ : (ptF₁ S s u).1 = t₁) (K : u.1.ExtraLevel N) (p : SecIdx t₁) :
    (p.1.1 : (Spec (CommRingCat.of S)).Opens).toScheme ⟶ M N hM₁ hN hm' hloc :=
  p.1.1.2.isoSpec.hom ≫
    ((datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring t₁ p) (φW t₁ p) (uW t₁ u p) (uW_isPullback_uof hM₁ t₁ s u ht₁ p)
      (KW N t₁ u K p)).1 ≫
    colimit.ι (gluingData N hM₁ hN hm' hloc).functor p.1.2

include hM₁ hN hm' hloc in
theorem piece_comp_fM (ht₁ : (ptF₁ S s u).1 = t₁) (K : u.1.ExtraLevel N) (p : SecIdx t₁) :
    piece N hM₁ hN hm' hloc t₁ s u ht₁ K p ≫ fM N hM₁ hN hm' hloc = (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ t₁ := by
  have sq := ((gluingData N hM₁ hN hm' hloc).isPullback_natTrans_ι_toBase p.1.2).w
  have h2 := reassoc_of% ((datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring t₁ p) (φW t₁ p) (uW t₁ u p)
      (uW_isPullback_uof hM₁ t₁ s u ht₁ p) (KW N t₁ u K p)).2
  have h3 := reassoc_of% (spec_φW_chartι t₁ p)
  simp only [piece, fM, Category.assoc]
  refine Eq.trans (congrArg (fun k => p.1.1.2.isoSpec.hom ≫
    ((datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring t₁ p) (φW t₁ p) (uW t₁ u p)
      (uW_isPullback_uof hM₁ t₁ s u ht₁ p) (KW N t₁ u K p)).1 ≫ k) sq.symm) ?_
  change p.1.1.2.isoSpec.hom ≫ _ ≫ ((datum N hM₁ hN hm' hloc p.1.2).ζ ≫ p.1.2.2.isoSpec.inv) ≫ (p.1.2 : M₁.Opens).ι = _
  rw [Category.assoc, h2, show p.1.2.2.isoSpec.inv ≫ (p.1.2 : M₁.Opens).ι = chartι p.1.2 from rfl, spec_φW_chartι]
  simp only [Wι, Category.assoc, Iso.hom_inv_id_assoc]

include hM₁ hN hm' hloc in

theorem piece_compat (ht₁ : (ptF₁ S s u).1 = t₁) (K : u.1.ExtraLevel N) {p q : (secCover t₁).I₀} (hpq : p ⟶ q) :
    Scheme.Cover.trans (secCover t₁) hpq ≫ piece N hM₁ hN hm' hloc t₁ s u ht₁ K q =
      piece N hM₁ hN hm' hloc t₁ s u ht₁ K p := by
  have h : p ≤ q := leOfHom hpq
  obtain ⟨g, hcomp, hvia, hP⟩ := exists_gpq t₁ u h
  have hWq : FakeEllipticCurve.WithFullLevel.IsPullback (ρW _ h) (uW t₁ u q) (uW t₁ u p) := by
    obtain ⟨hg, hm, ha, hl⟩ := hvia; exact ⟨g, hg, hm, ha, hl, hP⟩
  have hK : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of (Wring t₁ p))) (P : SchemeHomOver t (uW t₁ u p).1.f),
      FactorsThrough (KW N t₁ u K p).levK P →
        ∃ P₀ : X ⟶ (KW N t₁ u K q).K, P₀ ≫ (KW N t₁ u K q).levK = P.1 ≫ g := by
    intro X t P hPK
    obtain ⟨P₀, hP₀⟩ := (KW_spec N t₁ u K p t P).mp hPK
    have h2 := (KW_spec N t₁ u K q (t ≫ Spec.map (CommRingCat.ofHom (ρW _ h)))
      ⟨P.1 ≫ g, by rw [Category.assoc, hvia.1.w, ← Category.assoc, P.2]⟩).mpr
      ⟨P₀, by rw [hP₀]; simp only [Category.assoc, hcomp]⟩
    exact h2
  have hu'' : FakeEllipticCurve.WithFullLevel.IsPullback ((ρW _ h).comp (φW t₁ q)) (uof hM₁ q.1.2) (uW t₁ u p) :=
    isPullback_comp _ _ _ _ _ (uW_isPullback_uof hM₁ t₁ s u ht₁ q) hWq
  have law2 := (datum N hM₁ hN hm' hloc q.1.2).represents.2.1 (Wring t₁ q) (Wring t₁ p) (φW t₁ q) (ρW _ h)
    (uW t₁ u q) (uW t₁ u p) (uW_isPullback_uof hM₁ t₁ s u ht₁ q) hu'' (KW N t₁ u K q) (KW N t₁ u K p) g hvia hP hK

  have hU : (p.1.2 : M₁.directedAffineCover.I₀) ⟶ q.1.2 := homOfLE h.2
  have hw := colimit.w (gluingData N hM₁ hN hm' hloc).functor hU
  have hu₃ : FakeEllipticCurve.WithFullLevel.IsPullback ((φW t₁ p).comp (resRing h.2)) (uof hM₁ q.1.2) (uW t₁ u p) :=
    isPullback_comp _ _ _ _ _ (uof_isPullback hM₁ h.2) (uW_isPullback_uof hM₁ t₁ s u ht₁ p)
  have ht := (transZ_spec N hM₁ hN hm' hloc h.2).2 (Wring t₁ p) (φW t₁ p) (uW t₁ u p)
    (uW_isPullback_uof hM₁ t₁ s u ht₁ p) hu₃ (KW N t₁ u K p)
  change (Spec (CommRingCat.of S)).homOfLE h.1 ≫ q.1.1.2.isoSpec.hom ≫ _ ≫ _ = p.1.1.2.isoSpec.hom ≫ _ ≫ _
  rw [← Category.assoc, homOfLE_isoSpec_W t₁ h, Category.assoc]
  have eL := congrArg (fun k => p.1.1.2.isoSpec.hom ≫ k ≫ colimit.ι (gluingData N hM₁ hN hm' hloc).functor q.1.2) law2
  try simp only [Category.assoc] at eL
  refine eL.symm.trans ?_
  have eR := congrArg (fun k => p.1.1.2.isoSpec.hom ≫
    ((datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring t₁ p) (φW t₁ p) (uW t₁ u p)
      (uW_isPullback_uof hM₁ t₁ s u ht₁ p) (KW N t₁ u K p)).1 ≫ k) hw
  refine Eq.trans ?_ eR
  change _ = p.1.1.2.isoSpec.hom ≫ _ ≫ transZ N hM₁ hN hm' hloc h.2 ≫ colimit.ι (gluingData N hM₁ hN hm' hloc).functor q.1.2
  rw [reassoc_of% ht]
  congr 2
  exact (datum N hM₁ hN hm' hloc q.1.2).ptZ_congr N (ρW_comp_φW _ h) _ _ _ _

include hM₁ hN hm' hloc in

noncomputable def secOf (ht₁ : (ptF₁ S s u).1 = t₁) (K : u.1.ExtraLevel N) :
    Spec (CommRingCat.of S) ⟶ M N hM₁ hN hm' hloc :=
  (secCover t₁).glueMorphismsOfLocallyDirected (piece N hM₁ hN hm' hloc t₁ s u ht₁ K)
    (fun hpq => piece_compat N hM₁ hN hm' hloc t₁ s u ht₁ K hpq)

include hM₁ hN hm' hloc in
theorem ι_secOf (ht₁ : (ptF₁ S s u).1 = t₁) (K : u.1.ExtraLevel N) (p : SecIdx t₁) :
    (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ secOf N hM₁ hN hm' hloc t₁ s u ht₁ K =
      piece N hM₁ hN hm' hloc t₁ s u ht₁ K p :=
  (secCover t₁).map_glueMorphismsOfLocallyDirected _ _ p

include hM₁ hN hm' hloc in
theorem secOf_comp_fM (ht₁ : (ptF₁ S s u).1 = t₁) (K : u.1.ExtraLevel N) :
    secOf N hM₁ hN hm' hloc t₁ s u ht₁ K ≫ fM N hM₁ hN hm' hloc = t₁ := by
  apply (secCover t₁).hom_ext
  intro p
  change (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ _ = (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ _
  rw [← Category.assoc, ι_secOf, piece_comp_fM]

end Pieces

end Sec

omit hM₁ in
theorem isPullbackVia_comp {N' : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N' S) (E' : FakeEllipticCurve Λ N' S') (E'' : FakeEllipticCurve Λ N' S'')
    (g' : E'.A ⟶ E.A) (g'' : E''.A ⟶ E'.A)
    (h' : FakeEllipticCurve.IsPullbackVia φ E E' g') (h'' : FakeEllipticCurve.IsPullbackVia ψ E' E'' g'') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E'' (g'' ≫ g') := by
  obtain ⟨hg', mul', act', lev'⟩ := h'
  obtain ⟨hg'', mul'', act'', lev''⟩ := h''
  have hSpec : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have sq : IsPullback (g'' ≫ g') E''.f E.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hSpec]; exact hg''.paste_horiz hg'
  refine ⟨sq, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [← Category.assoc, mul'' t P Q, mul' (t ≫ Spec.map (CommRingCat.ofHom ψ))]
    exact mul_val_congr E.L (by rw [hSpec, Category.assoc]) _ _ _ _ (by simp [Category.assoc]) (by simp [Category.assoc])
  · intro x
    rw [← Category.assoc, act'' x, Category.assoc, act' x, Category.assoc]
  · intro T t P hP
    obtain ⟨P₀, hP₀⟩ := lev'' t P hP
    obtain ⟨P₁, hP₁⟩ := lev' (t ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1 ≫ g'', by
      rw [Category.assoc, hg''.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    exact ⟨P₁, by rw [hP₁, Category.assoc]⟩

section SecPullback

variable {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
  (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪))
  (hs : Spec.map (CommRingCat.ofHom φ) ≫ s = s')
  (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m S')
  (G : u'.1.A ⟶ u.1.A) (hG : FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 G)
  (hGP : (u'.2.P).1 ≫ G = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
  (K : u.1.ExtraLevel N) (K' : u'.1.ExtraLevel N)
  (hKK' : ∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
    FactorsThrough K'.levK P → ∃ P₀ : X ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ G)
  {t₁ : Spec (CommRingCat.of S) ⟶ M₁} (ht₁ : (ptF₁ S s u).1 = t₁)
  {t₁' : Spec (CommRingCat.of S') ⟶ M₁} (ht₁' : (ptF₁ S' s' u').1 = t₁')

include hM₁ hG hGP hs ht₁ ht₁' in
theorem t₁'_eq : t₁' = Spec.map (CommRingCat.ofHom φ) ≫ t₁ := by
  have h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by
    obtain ⟨hg, hm, ha, hl⟩ := hG; exact ⟨G, hg, hm, ha, hl, hGP⟩
  rw [← ht₁, ← ht₁']
  exact hM₁.ptF_pullback _ _ φ s s' hs u u' h

def PBIdx : Type :=
  {j : SecIdx t₁' × (Spec (CommRingCat.of S)).affineOpens //
    (j.1.1.1 : (Spec (CommRingCat.of S')).Opens) ≤ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (j.2 : (Spec (CommRingCat.of S)).Opens) ∧
    (j.2 : (Spec (CommRingCat.of S)).Opens) ≤ t₁ ⁻¹ᵁ (j.1.1.2 : M₁.Opens)}

def PBIdx.toSec (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) : SecIdx t₁ := ⟨(j.1.2, j.1.1.1.2), j.2.2⟩

include hM₁ hG hGP hs ht₁ ht₁' in
theorem exists_pbIdx (x : ↥(Spec (CommRingCat.of S'))) :
    ∃ j : PBIdx φ (t₁ := t₁) (t₁' := t₁'), x ∈ (j.1.1.1.1 : (Spec (CommRingCat.of S')).Opens) := by
  have ht := t₁'_eq hM₁ φ s s' hs u u' G hG hGP ht₁ ht₁'
  let y := Spec.map (CommRingCat.ofHom φ) x
  obtain ⟨p, hyp, -, -⟩ := exists_secIdx t₁ y ⊤ trivial ⊤ trivial
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'le⟩ := (Spec (CommRingCat.of S')).isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (p.1.1 : (Spec (CommRingCat.of S)).Opens) from hyp)
    ((Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (p.1.1 : (Spec (CommRingCat.of S)).Opens)).2
  have hp' : (W' : (Spec (CommRingCat.of S')).Opens) ≤ t₁' ⁻¹ᵁ (p.1.2 : M₁.Opens) := by
    intro z hz
    have := p.2 (hW'le hz)
    simpa [ht, Scheme.Hom.comp_base] using this
  exact ⟨⟨(⟨(⟨W', hW'⟩, p.1.2), hp'⟩, p.1.1), hW'le, p.2⟩, hxW'⟩

include hM₁ hG hGP hs ht₁ ht₁' in

noncomputable def pbCover : (Spec (CommRingCat.of S')).OpenCover :=
  Scheme.Cover.mkOfCovers (PBIdx φ (t₁ := t₁) (t₁' := t₁')) (fun j => j.1.1.1.1)
    (fun j => (j.1.1.1.1 : (Spec (CommRingCat.of S')).Opens).ι)
    (fun x => by
      obtain ⟨j, hx⟩ := exists_pbIdx hM₁ φ s s' hs u u' G hG hGP ht₁ ht₁' x
      exact ⟨j, ⟨x, hx⟩, rfl⟩)

noncomputable def rl (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) :
    (j.1.1.1.1 : (Spec (CommRingCat.of S')).Opens).toScheme ⟶
      ((PBIdx.toSec φ j).1.1 : (Spec (CommRingCat.of S)).Opens).toScheme :=
  (Spec.map (CommRingCat.ofHom φ)).resLE _ _ j.2.1

noncomputable def rlSpec (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) :
    Spec (CommRingCat.of (Wring t₁' j.1.1)) ⟶ Spec (CommRingCat.of (Wring t₁ (PBIdx.toSec φ j))) :=
  j.1.1.1.1.2.isoSpec.inv ≫ rl φ j ≫ (PBIdx.toSec φ j).1.1.2.isoSpec.hom

noncomputable def ψj (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) : Wring t₁ (PBIdx.toSec φ j) →+* Wring t₁' j.1.1 :=
  (Spec.preimage (rlSpec φ j)).hom

theorem spec_ψj (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) : Spec.map (CommRingCat.ofHom (ψj φ j)) = rlSpec φ j := by
  simp [ψj]

theorem rl_isoSpec (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) :
    rl φ j ≫ (PBIdx.toSec φ j).1.1.2.isoSpec.hom = j.1.1.1.1.2.isoSpec.hom ≫ rlSpec φ j := by
  simp only [rlSpec, Iso.hom_inv_id_assoc]

theorem ψj_comp_rW (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) :
    (ψj φ j).comp (rW t₁ (PBIdx.toSec φ j)) = (rW t₁' j.1.1).comp φ := by
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, spec_rW, spec_rW, spec_ψj φ j]
  change (j.1.1.1.1.2.isoSpec.inv ≫ rl φ j ≫ (PBIdx.toSec φ j).1.1.2.isoSpec.hom) ≫ (PBIdx.toSec φ j).1.1.2.isoSpec.inv ≫
      ((PBIdx.toSec φ j).1.1 : (Spec (CommRingCat.of S)).Opens).ι =
    (j.1.1.1.1.2.isoSpec.inv ≫ (j.1.1.1.1 : (Spec (CommRingCat.of S')).Opens).ι) ≫ Spec.map (CommRingCat.ofHom φ)
  simp only [rl, Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]

include hM₁ hG hGP hs ht₁ ht₁' in
theorem ψj_comp_φW (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) :
    (ψj φ j).comp (φW t₁ (PBIdx.toSec φ j)) = φW t₁' j.1.1 := by
  have ht := t₁'_eq hM₁ φ s s' hs u u' G hG hGP ht₁ ht₁'
  apply ringHom_eq_of_spec_map_eq
  rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_ψj φ j]
  change rlSpec φ j ≫ Spec.map (CommRingCat.ofHom (φW t₁ (PBIdx.toSec φ j))) = Spec.map (CommRingCat.ofHom (φW t₁' j.1.1))
  rw [spec_φW t₁ (PBIdx.toSec φ j), spec_φW t₁' j.1.1]
  change (j.1.1.1.1.2.isoSpec.inv ≫ rl φ j ≫ (PBIdx.toSec φ j).1.1.2.isoSpec.hom) ≫ (PBIdx.toSec φ j).1.1.2.isoSpec.inv ≫
      cmap t₁ (PBIdx.toSec φ j) ≫ (PBIdx.toSec φ j).1.2.2.isoSpec.hom =
    j.1.1.1.1.2.isoSpec.inv ≫ cmap t₁' j.1.1 ≫ j.1.1.1.2.2.isoSpec.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  have key : (rl φ j ≫ t₁.resLE _ _ (PBIdx.toSec φ j).2) ≫ ((PBIdx.toSec φ j).1.2 : M₁.Opens).ι =
      t₁'.resLE _ _ j.1.1.2 ≫ (j.1.1.1.2 : M₁.Opens).ι := by
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc, Scheme.Hom.resLE_comp_ι, rl, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, ← ht]
  exact (cancel_mono ((PBIdx.toSec φ j).1.2 : M₁.Opens).ι).mp key

include hM₁ hN hm' hloc hG hGP hs hKK' in

theorem piece_pullback (j : PBIdx φ (t₁ := t₁) (t₁' := t₁')) :
    piece N hM₁ hN hm' hloc t₁' s' u' ht₁' K' j.1.1 =
      rl φ j ≫ piece N hM₁ hN hm' hloc t₁ s u ht₁ K (PBIdx.toSec φ j) := by
  set p := PBIdx.toSec φ j
  set p' := j.1.1

  have hχ := ψj_comp_rW φ j
  obtain ⟨g, hcomp, hf, -, hvia⟩ :=
    FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq (rW t₁ p) (ψj φ j)
      ((rW t₁' p').comp φ) hχ u.1 (uW t₁ u p).1 (uW t₁' u' p').1 (gW t₁ u p) (gW_via t₁ u p).1
      (hlev'_level_one (rW t₁ p) u.1 (uW t₁ u p).1 (gW t₁ u p) (gW_via t₁ u p).1) (gW t₁' u' p' ≫ G)
      (isPullbackVia_comp φ (rW t₁' p') u.1 u'.1 (uW t₁' u' p').1 G (gW t₁' u' p') hG (gW_via t₁' u' p').1)
  have hSpecχ : Spec.map (CommRingCat.ofHom (ψj φ j)) ≫ Spec.map (CommRingCat.ofHom (rW t₁ p)) =
      Spec.map (CommRingCat.ofHom (rW t₁' p')) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ, CommRingCat.ofHom_comp, Spec.map_comp]
  have hP : ((uW t₁' u' p').2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (ψj φ j)) ≫ ((uW t₁ u p).2.P).1 := by
    apply (gW_via t₁ u p).1.1.hom_ext
    · rw [Category.assoc, hcomp, ← Category.assoc, (gW_via t₁' u' p').2, Category.assoc, hGP, Category.assoc,
        (gW_via t₁ u p).2, ← Category.assoc, ← Category.assoc, hSpecχ]
    · rw [Category.assoc, hf, ← Category.assoc, ((uW t₁' u' p').2.P).2, Category.assoc, ((uW t₁ u p).2.P).2]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hWq : FakeEllipticCurve.WithFullLevel.IsPullback (ψj φ j) (uW t₁ u p) (uW t₁' u' p') := by
    obtain ⟨hg, hm, ha, hl⟩ := hvia; exact ⟨g, hg, hm, ha, hl, hP⟩
  have hK : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of (Wring t₁' p'))) (P : SchemeHomOver t (uW t₁' u' p').1.f),
      FactorsThrough (KW N t₁' u' K' p').levK P →
        ∃ P₀ : X ⟶ (KW N t₁ u K p).K, P₀ ≫ (KW N t₁ u K p).levK = P.1 ≫ g := by
    intro X t P hPK
    have h1 := (KW_spec N t₁' u' K' p' t P).mp hPK
    obtain ⟨Q₀, hQ₀⟩ := hKK' _ _ h1
    have h2 := (KW_spec N t₁ u K p (t ≫ Spec.map (CommRingCat.ofHom (ψj φ j)))
      ⟨P.1 ≫ g, by rw [Category.assoc, hvia.1.w, ← Category.assoc, P.2]⟩).mpr
      ⟨Q₀, by rw [hQ₀]; simp only [Category.assoc, hcomp]⟩
    exact h2
  have hu'' : FakeEllipticCurve.WithFullLevel.IsPullback ((ψj φ j).comp (φW t₁ p)) (uof hM₁ p.1.2) (uW t₁' u' p') :=
    isPullback_comp _ _ _ _ _ (uW_isPullback_uof hM₁ t₁ s u ht₁ p) hWq
  have law2 := (datum N hM₁ hN hm' hloc p.1.2).represents.2.1 (Wring t₁ p) (Wring t₁' p') (φW t₁ p) (ψj φ j)
    (uW t₁ u p) (uW t₁' u' p') (uW_isPullback_uof hM₁ t₁ s u ht₁ p) hu'' (KW N t₁ u K p) (KW N t₁' u' K' p') g
    hvia hP hK

  change p'.1.1.2.isoSpec.hom ≫ _ ≫ _ = rl φ j ≫ p.1.1.2.isoSpec.hom ≫ _ ≫ _
  rw [← Category.assoc (rl φ j), rl_isoSpec φ j, Category.assoc, ← spec_ψj φ j]
  have eR := congrArg (fun k => p'.1.1.2.isoSpec.hom ≫ k ≫ colimit.ι (gluingData N hM₁ hN hm' hloc).functor p.1.2) law2
  try simp only [Category.assoc] at eR
  refine Eq.trans ?_ eR
  congr 2
  exact (datum N hM₁ hN hm' hloc p.1.2).ptZ_congr N (ψj_comp_φW hM₁ φ s s' hs u u' G hG hGP ht₁ ht₁' j).symm _ _ _ _

include hM₁ hN hm' hloc hG hGP hs hKK' in

theorem secOf_pullback :
    secOf N hM₁ hN hm' hloc t₁' s' u' ht₁' K' = Spec.map (CommRingCat.ofHom φ) ≫ secOf N hM₁ hN hm' hloc t₁ s u ht₁ K := by
  apply (pbCover hM₁ φ s s' hs u u' G hG hGP ht₁ ht₁').hom_ext
  intro j
  change (j.1.1.1.1 : (Spec (CommRingCat.of S')).Opens).ι ≫ _ = (j.1.1.1.1 : (Spec (CommRingCat.of S')).Opens).ι ≫ _
  rw [ι_secOf, piece_pullback N hM₁ hN hm' hloc φ s s' hs u u' G hG hGP K K' hKK' ht₁ ht₁' j,
    ← ι_secOf N hM₁ hN hm' hloc t₁ s u ht₁ K (PBIdx.toSec φ j)]
  change rl φ j ≫ ((PBIdx.toSec φ j).1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ _ = _
  rw [← Category.assoc, rl, Scheme.Hom.resLE_comp_ι, Category.assoc]

end SecPullback

section PtF

variable {S : Type} [CommRing S]

structure Lev1Data (w : FakeEllipticCurve.WithFullLevel Λ N m S) where
  E₁ : FakeEllipticCurve Λ 1 S
  K : E₁.ExtraLevel N
  e : w.1.A ≅ E₁.A
  he : e.hom ≫ E₁.f = w.1.f
  hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t w.1.f),
    mapPt e.hom he (w.1.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)
  hact : ∀ x : ↥Λ, w.1.act x ≫ e.hom = e.hom ≫ E₁.act x
  hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t w.1.f),
    FactorsThrough w.1.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P)
  P₁ : E₁.FullLevel m
  hP₁ : P₁.P = mapPt e.hom he w.2.P

theorem nonempty_lev1Data (w : FakeEllipticCurve.WithFullLevel Λ N m S) : Nonempty (Lev1Data (Λ := Λ) N w) := by
  obtain ⟨E₁, K, e, he, hmul, hact, hlev⟩ :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelOne_extraLevel_and_exists_of_extraLevel Λ N S).1 w.1
  obtain ⟨P₁, hP₁⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt w.1 E₁ e he hmul hact w.2
  exact ⟨⟨E₁, K, e, he, hmul, hact, hlev, P₁, hP₁⟩⟩

noncomputable def lev1Data (w : FakeEllipticCurve.WithFullLevel Λ N m S) : Lev1Data (Λ := Λ) N w :=
  (nonempty_lev1Data N w).some

noncomputable abbrev lev1 (w : FakeEllipticCurve.WithFullLevel Λ N m S) : FakeEllipticCurve.WithFullLevel Λ 1 m S :=
  ⟨(lev1Data N w).E₁, (lev1Data N w).P₁⟩

include hM₁ hN hm' hloc in

noncomputable def ptFM (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (w : FakeEllipticCurve.WithFullLevel Λ N m S) :
    SchemeHomOver s (fM N hM₁ hN hm' hloc ≫ π₁) :=
  ⟨secOf N hM₁ hN hm' hloc (ptF₁ S s (lev1 N w)).1 s (lev1 N w) rfl (lev1Data N w).K, by
    rw [← Category.assoc, secOf_comp_fM]; exact (ptF₁ S s (lev1 N w)).2⟩

end PtF

section PullbackLaw

omit hM₁ in

theorem mapPt_inv_mul {N₁ N₂ : ℕ} {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N₁ S) (E' : FakeEllipticCurve Λ N₂ S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f) (he' : e.inv ≫ E.f = E'.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f) :
    mapPt e.inv he' (E'.L.mul t P Q) = E.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
  have h := hmul t (mapPt e.inv he' P) (mapPt e.inv he' Q)
  have hP : mapPt e.hom he (mapPt e.inv he' P) = P := Subtype.ext (by simp [mapPt_coe])
  have hQ : mapPt e.hom he (mapPt e.inv he' Q) = Q := Subtype.ext (by simp [mapPt_coe])
  rw [hP, hQ] at h
  apply Subtype.ext
  simp only [mapPt_coe]
  rw [← h]
  simp [mapPt_coe]

omit hM₁ in

theorem lev_to_lev_level_one {T T' : Type} [CommRing T] [CommRing T'] (φ : T →+* T')
    (E : FakeEllipticCurve Λ 1 T) (E' : FakeEllipticCurve Λ 1 T') (G : E'.A ⟶ E.A)
    (hG : IsPullback G E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T')) (P Q : SchemeHomOver t E'.f),
      (E'.L.mul t P Q).1 ≫ G =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ G, by rw [Category.assoc, hG.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ G, by rw [Category.assoc, hG.w, ← Category.assoc, Q.2]⟩).1) :
    ∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t' E'.f),
      FactorsThrough E'.lev P → ∃ P₀ : X ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ G := by
  intro X t' P hP
  rw [lev1_iff] at hP
  subst hP
  obtain ⟨P₀, hP₀⟩ := E.lev_one (t' ≫ Spec.map (CommRingCat.ofHom φ))
  exact ⟨P₀, by rw [hP₀, one_comp_of_mul φ E E' G hG hmul t']⟩

theorem lev1_comparison {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (w' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ w w') :
    ∃ G : (lev1 N w').1.A ⟶ (lev1 N w).1.A,
      FakeEllipticCurve.IsPullbackVia φ (lev1 N w).1 (lev1 N w').1 G ∧
      ((lev1 N w').2.P).1 ≫ G = Spec.map (CommRingCat.ofHom φ) ≫ ((lev1 N w).2.P).1 ∧
      ∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' (lev1 N w').1.f),
        FactorsThrough (lev1Data N w').K.levK P →
          ∃ P₀ : X ⟶ (lev1Data N w).K.K, P₀ ≫ (lev1Data N w).K.levK = P.1 ≫ G := by
  obtain ⟨g₀, hg₀, mul₀, act₀, lev₀, P₀⟩ := h
  set d := lev1Data N w
  set d' := lev1Data N w'
  have he'inv : d'.e.inv ≫ w'.1.f = d'.E₁.f := by rw [← d'.he, Iso.inv_hom_id_assoc]
  let G : d'.E₁.A ⟶ d.E₁.A := d'.e.inv ≫ g₀ ≫ d.e.hom
  have sq1 : IsPullback d'.e.inv d'.E₁.f w'.1.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [he'inv, Category.comp_id]⟩
  have sq3 : IsPullback d.e.hom w.1.f d.E₁.f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [d.he, Category.comp_id]⟩
  have sq : IsPullback G d'.E₁.f d.E₁.f (Spec.map (CommRingCat.ofHom φ)) := by
    simpa using (sq1.paste_horiz hg₀).paste_horiz sq3
  have hmulG : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t d'.E₁.f),
      (d'.E₁.L.mul t P Q).1 ≫ G =
        (d.E₁.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ G, by rw [Category.assoc, sq.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ G, by rw [Category.assoc, sq.w, ← Category.assoc, Q.2]⟩).1 := by
    intro X t P Q
    have h1 := congrArg Subtype.val (mapPt_inv_mul w'.1 d'.E₁ d'.e d'.he he'inv d'.hmul t P Q)
    simp only [mapPt_coe] at h1
    have h2 := mul₀ t (mapPt d'.e.inv he'inv P) (mapPt d'.e.inv he'inv Q)
    have h3 := fun (A B : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) w.1.f) =>
      congrArg Subtype.val (d.hmul _ A B)
    simp only [mapPt_coe] at h3
    simp only [G, ← Category.assoc]
    rw [h1, h2, h3]
    exact mul_val_congr d.E₁.L rfl _ _ _ _ (by simp [Category.assoc]) (by simp [Category.assoc])
  refine ⟨G, ⟨sq, hmulG, ?_, ?_⟩, ?_, ?_⟩
  · intro x
    have h1 : d'.E₁.act x ≫ d'.e.inv = d'.e.inv ≫ w'.1.act x := by
      rw [← cancel_epi d'.e.hom, ← Category.assoc, ← d'.hact x, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc]
    show d'.E₁.act x ≫ (d'.e.inv ≫ g₀ ≫ d.e.hom) = (d'.e.inv ≫ g₀ ≫ d.e.hom) ≫ d.E₁.act x
    simp only [Category.assoc]
    rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (w'.1.act x), act₀ x, Category.assoc, d.hact x]
  · exact lev_to_lev_level_one φ d.E₁ d'.E₁ G sq hmulG
  · show (d'.P₁.P).1 ≫ G = Spec.map (CommRingCat.ofHom φ) ≫ (d.P₁.P).1
    rw [d'.hP₁, d.hP₁, mapPt_coe, mapPt_coe]
    simp only [G, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, P₀, Category.assoc]
  · intro X t' P hP
    have hQ : FactorsThrough d'.K.levK (mapPt d'.e.hom d'.he (mapPt d'.e.inv he'inv P)) := by
      obtain ⟨P₁, hP₁⟩ := hP; exact ⟨P₁, by rw [hP₁]; simp [mapPt_coe]⟩
    have hw' := (d'.hlev t' (mapPt d'.e.inv he'inv P)).mpr hQ
    obtain ⟨Q₀, hQ₀⟩ := lev₀ t' _ hw'
    have hw : FactorsThrough w.1.lev (t := t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨(mapPt d'.e.inv he'inv P).1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, (mapPt d'.e.inv he'inv P).2]⟩ :=
      ⟨Q₀, hQ₀⟩
    obtain ⟨P₀', hP₀'⟩ := (d.hlev _ _).mp hw
    exact ⟨P₀', by rw [hP₀']; simp only [mapPt_coe, G, Category.assoc]⟩

include hM₁ hN hm' hloc in
theorem ptFM_pullback' (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪))
    (hs : Spec.map (CommRingCat.ofHom φ) ≫ s = s')
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (w' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ w w') :
    (ptFM N hM₁ hN hm' hloc s' w').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptFM N hM₁ hN hm' hloc s w).1 := by
  obtain ⟨G, hG, hGP, hKK'⟩ := lev1_comparison N φ w w' h
  exact secOf_pullback N hM₁ hN hm' hloc φ s s' hs (lev1 N w) (lev1 N w') G hG hGP (lev1Data N w).K (lev1Data N w').K
    hKK' rfl rfl

omit hM₁ in

theorem isPullback_id_of_iso {N' : ℕ} {S : Type} [CommRing S] (w w' : FakeEllipticCurve.WithFullLevel Λ N' m S)
    (h : FakeEllipticCurve.WithFullLevel.Iso w w') :
    FakeEllipticCurve.WithFullLevel.IsPullback (RingHom.id S) w w' := by
  obtain ⟨e, he, hmul, hact, hlev, hP⟩ := h
  have he' : e.inv ≫ w.1.f = w'.1.f := by rw [← he, Iso.inv_hom_id_assoc]
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have sq : IsPullback e.inv w'.1.f w.1.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hid]; exact IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  refine ⟨e.inv, sq, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    have h1 := congrArg Subtype.val (mapPt_inv_mul w.1 w'.1 e he he' hmul t P Q)
    simp only [mapPt_coe] at h1
    rw [h1]
    exact mul_val_congr w.1.L (by rw [hid, Category.comp_id]) _ _ _ _ (by simp) (by simp)
  · intro x
    rw [← cancel_epi e.hom, ← Category.assoc, ← hact x, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  · intro T t P hPl
    have : FactorsThrough w.1.lev (mapPt e.inv he' P) := by
      rw [hlev]
      obtain ⟨P₀, hP₀⟩ := hPl
      exact ⟨P₀, by rw [hP₀]; simp [mapPt_coe]⟩
    obtain ⟨P₀, hP₀⟩ := this
    exact ⟨P₀, by rw [hP₀, mapPt_coe]⟩
  · rw [← congrArg Subtype.val hP, mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id, hid, Category.id_comp]

include hM₁ hN hm' hloc in
theorem ptFM_iso' (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (w w' : FakeEllipticCurve.WithFullLevel Λ N m S) (h : FakeEllipticCurve.WithFullLevel.Iso w w') :
    ptFM N hM₁ hN hm' hloc s w = ptFM N hM₁ hN hm' hloc s w' := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have := ptFM_pullback' N hM₁ hN hm' hloc S S (RingHom.id S) s s (by rw [hid, Category.id_comp]) w w'
    (isPullback_id_of_iso w w' h)
  rw [hid, Category.id_comp] at this
  exact (Subtype.ext this).symm

end PullbackLaw

omit hM₁ in

theorem factorsThrough_of_openCover {C A T : Scheme.{0}} (i : C ⟶ A) [Mono i] (P : T ⟶ A) (𝒯 : T.OpenCover)
    (h : ∀ k, ∃ l : 𝒯.X k ⟶ C, l ≫ i = 𝒯.f k ≫ P) : ∃ l : T ⟶ C, l ≫ i = P := by
  choose l hl using h
  refine ⟨𝒯.glueMorphisms l fun k k' => ?_, ?_⟩
  · rw [← cancel_mono i, Category.assoc, hl, Category.assoc, hl, pullback.condition_assoc]
  · apply 𝒯.hom_ext
    intro k
    rw [← Category.assoc, 𝒯.ι_glueMorphisms, hl]

section InjK

variable {S : Type} [CommRing S] (t₁ : Spec (CommRingCat.of S) ⟶ M₁)
  (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)

include hM₁ hN hm' hloc in

theorem KW_iff_of_secOf_eq (ht₁ : (ptF₁ S s u).1 = t₁) (K K' : u.1.ExtraLevel N)
    (h : secOf N hM₁ hN hm' hloc t₁ s u ht₁ K = secOf N hM₁ hN hm' hloc t₁ s u ht₁ K') (p : SecIdx t₁)
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of (Wring t₁ p))) (Q : SchemeHomOver t (uW t₁ u p).1.f) :
    FactorsThrough (KW N t₁ u K p).levK Q ↔ FactorsThrough (KW N t₁ u K' p).levK Q := by
  have hp := ι_secOf N hM₁ hN hm' hloc t₁ s u ht₁ K p
  rw [h, ι_secOf] at hp

  have hoi : IsOpenImmersion (colimit.ι (gluingData N hM₁ hN hm' hloc).functor p.1.2) := by
    first | exact (gluingData N hM₁ hN hm' hloc).cover.map_prop p.1.2 | simpa using (gluingData N hM₁ hN hm' hloc).cover.map_prop p.1.2
  have hmono : Mono (colimit.ι (gluingData N hM₁ hN hm' hloc).functor p.1.2) := IsOpenImmersion.mono _
  simp only [piece, Category.assoc] at hp
  have hp2 := (cancel_epi _).mp hp
  have hp3 := hmono.right_cancellation _ _ hp2
  exact (datum N hM₁ hN hm' hloc p.1.2).represents.2.2.2 _ _ _ _ _ _ (Subtype.ext hp3).symm t Q

include hM₁ hN hm' hloc in

theorem factorsThrough_iff_of_secOf_eq (ht₁ : (ptF₁ S s u).1 = t₁) (K K' : u.1.ExtraLevel N)
    (h : secOf N hM₁ hN hm' hloc t₁ s u ht₁ K = secOf N hM₁ hN hm' hloc t₁ s u ht₁ K')
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f) :
    FactorsThrough K.levK P ↔ FactorsThrough K'.levK P := by

  have key : ∀ (K₁ K₂ : u.1.ExtraLevel N),
      (∀ (p : SecIdx t₁) {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of (Wring t₁ p))) (Q : SchemeHomOver t (uW t₁ u p).1.f),
        FactorsThrough (KW N t₁ u K₁ p).levK Q → FactorsThrough (KW N t₁ u K₂ p).levK Q) →
      FactorsThrough K₁.levK P → FactorsThrough K₂.levK P := by
    intro K₁ K₂ hloc12 hP
    haveI := K₂.levK_closed
    apply factorsThrough_of_openCover K₂.levK P.1 ((secCover t₁).pullback₁ t)
    intro p

    let tp : pullback t ((secCover t₁).f p) ⟶ Spec (CommRingCat.of (Wring t₁ p)) :=
      pullback.snd t ((secCover t₁).f p) ≫ p.1.1.2.isoSpec.hom
    have htp : tp ≫ Spec.map (CommRingCat.ofHom (rW t₁ p)) = pullback.fst t ((secCover t₁).f p) ≫ t := by
      simp only [tp, spec_rW, Wι, Category.assoc]
      erw [Iso.hom_inv_id_assoc]
      exact (pullback.condition (f := t) (g := (secCover t₁).f p)).symm
    have hsq := (gW_via t₁ u p).1.1
    let Q : pullback t ((secCover t₁).f p) ⟶ (uW t₁ u p).1.A :=
      hsq.lift (pullback.fst t ((secCover t₁).f p) ≫ P.1) tp (by rw [Category.assoc, P.2, htp])
    have hQ₁ : Q ≫ gW t₁ u p = pullback.fst t ((secCover t₁).f p) ≫ P.1 := hsq.lift_fst _ _ _
    have hQ₂ : Q ≫ (uW t₁ u p).1.f = tp := hsq.lift_snd _ _ _
    have hQK₁ : FactorsThrough (KW N t₁ u K₁ p).levK ⟨Q, hQ₂⟩ := by
      refine (KW_spec N t₁ u K₁ p tp ⟨Q, hQ₂⟩).mpr ?_
      obtain ⟨P₀, hP₀⟩ := hP
      exact ⟨pullback.fst t ((secCover t₁).f p) ≫ P₀, by simp only [Category.assoc, hP₀, hQ₁]⟩
    obtain ⟨l, hl⟩ := (KW_spec N t₁ u K₂ p tp ⟨Q, hQ₂⟩).mp (hloc12 p tp ⟨Q, hQ₂⟩ hQK₁)
    exact ⟨l, hl.trans hQ₁⟩
  constructor
  · exact key K K' fun p X t Q => (KW_iff_of_secOf_eq N hM₁ hN hm' hloc t₁ s u ht₁ K K' h p t Q).mp
  · exact key K' K fun p X t Q => (KW_iff_of_secOf_eq N hM₁ hN hm' hloc t₁ s u ht₁ K K' h p t Q).mpr

end InjK

section InjLaw

omit hM₁ in
theorem factorsThrough_congr {R : Type} [CommRing R] {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (lev : C ⟶ A)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t₁ f) (Q : SchemeHomOver t₂ f)
    (h : P.1 = Q.1) : FactorsThrough lev P ↔ FactorsThrough lev Q := by
  unfold FactorsThrough; rw [h]

omit hM₁ in

theorem isPullbackVia_inv_of_iso {N' : ℕ} {S : Type} [CommRing S] (w w' : FakeEllipticCurve.WithFullLevel Λ N' m S)
    (e : w.1.A ≅ w'.1.A) (he : e.hom ≫ w'.1.f = w.1.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t w.1.f),
      mapPt e.hom he (w.1.L.mul t P Q) = w'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, w.1.act x ≫ e.hom = e.hom ≫ w'.1.act x)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t w.1.f),
      FactorsThrough w.1.lev P ↔ FactorsThrough w'.1.lev (mapPt e.hom he P))
    (hP : mapPt e.hom he w.2.P = w'.2.P) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) w.1 w'.1 e.inv ∧
      (w'.2.P).1 ≫ e.inv = Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ (w.2.P).1 := by
  have he' : e.inv ≫ w.1.f = w'.1.f := by rw [← he, Iso.inv_hom_id_assoc]
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have sq : IsPullback e.inv w'.1.f w.1.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hid]; exact IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  refine ⟨⟨sq, ?_, ?_, ?_⟩, ?_⟩
  · intro T t P Q
    have h1 := congrArg Subtype.val (mapPt_inv_mul w.1 w'.1 e he he' hmul t P Q)
    simp only [mapPt_coe] at h1
    rw [h1]
    exact mul_val_congr w.1.L (by rw [hid, Category.comp_id]) _ _ _ _ (by simp) (by simp)
  · intro x
    rw [← cancel_epi e.hom, ← Category.assoc, ← hact x, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  · intro T t P hPl
    have : FactorsThrough w.1.lev (mapPt e.inv he' P) := by
      rw [hlev]
      obtain ⟨P₀, hP₀⟩ := hPl
      exact ⟨P₀, by rw [hP₀]; simp [mapPt_coe]⟩
    obtain ⟨P₀, hP₀⟩ := this
    exact ⟨P₀, by rw [hP₀, mapPt_coe]⟩
  · rw [← congrArg Subtype.val hP, mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id, hid, Category.id_comp]

include hM₁ hN hm' hloc in
theorem ptFM_injective' (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (w w' : FakeEllipticCurve.WithFullLevel Λ N m S) (h : ptFM N hM₁ hN hm' hloc s w = ptFM N hM₁ hN hm' hloc s w') :
    FakeEllipticCurve.WithFullLevel.Iso w w' := by
  set d := lev1Data N w
  set d' := lev1Data N w'
  have h1 : secOf N hM₁ hN hm' hloc (ptF₁ S s (lev1 N w)).1 s (lev1 N w) rfl d.K =
      secOf N hM₁ hN hm' hloc (ptF₁ S s (lev1 N w')).1 s (lev1 N w') rfl d'.K := congrArg Subtype.val h

  have hM₁pt : ptF₁ S s (lev1 N w) = ptF₁ S s (lev1 N w') := by
    apply Subtype.ext
    rw [← secOf_comp_fM N hM₁ hN hm' hloc (ptF₁ S s (lev1 N w)).1 s (lev1 N w) rfl d.K,
      ← secOf_comp_fM N hM₁ hN hm' hloc (ptF₁ S s (lev1 N w')).1 s (lev1 N w') rfl d'.K, h1]
  obtain ⟨e, he, emul, eact, elev, eP⟩ := hM₁.ptF_injective _ _ _ _ hM₁pt
  obtain ⟨hvia, gP⟩ := isPullbackVia_inv_of_iso (lev1 N w) (lev1 N w') e he emul eact elev eP

  obtain ⟨K'', hK''⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (RingHom.id S) (lev1 N w).1 (lev1 N w').1 e.inv hvia N d.K
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have e3 := secOf_pullback N hM₁ hN hm' hloc (RingHom.id S) s s (by rw [hid, Category.id_comp]) (lev1 N w) (lev1 N w')
    e.inv hvia gP d.K K'' (fun t' P hP => (hK'' t' P).mp hP) rfl rfl
  rw [hid, Category.id_comp] at e3
  have hKK := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t (lev1 N w').1.f) =>
    factorsThrough_iff_of_secOf_eq N hM₁ hN hm' hloc (ptF₁ S s (lev1 N w')).1 s (lev1 N w') rfl K'' d'.K (e3.trans h1) t P

  have he'inv : d'.e.inv ≫ w'.1.f = d'.E₁.f := by rw [← d'.he, Iso.inv_hom_id_assoc]
  have he₂ : e.hom ≫ d'.E₁.f = d.E₁.f := he
  let Θ : w.1.A ≅ w'.1.A := d.e ≪≫ e ≪≫ d'.e.symm
  have hΘ : Θ.hom ≫ w'.1.f = w.1.f := by
    simp only [Θ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [he'inv, he₂, d.he]
  have hΘ₁ : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t w.1.f),
      (mapPt Θ.hom hΘ P).1 = P.1 ≫ d.e.hom ≫ e.hom ≫ d'.e.inv := by
    intro T t P; simp only [mapPt_coe, Θ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  refine ⟨Θ, hΘ, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    apply Subtype.ext
    have h₁ := congrArg Subtype.val (d.hmul t P Q)
    have h₂ := fun (A B : SchemeHomOver t d.E₁.f) => congrArg Subtype.val (emul t A B)
    have h₃ := fun (A B : SchemeHomOver t d'.E₁.f) =>
      congrArg Subtype.val (mapPt_inv_mul w'.1 d'.E₁ d'.e d'.he he'inv d'.hmul t A B)
    simp only [mapPt_coe] at h₁ h₂ h₃
    rw [hΘ₁, reassoc_of% h₁, reassoc_of% (h₂ _ _), h₃]
    exact mul_val_congr w'.1.L rfl _ _ _ _ (by rw [hΘ₁]; simp only [mapPt_coe, Category.assoc])
      (by rw [hΘ₁]; simp only [mapPt_coe, Category.assoc])
  · intro x
    have h₃ : d'.E₁.act x ≫ d'.e.inv = d'.e.inv ≫ w'.1.act x := by
      rw [← cancel_epi d'.e.hom, ← Category.assoc, ← d'.hact x, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc]
    have h₂ : d.E₁.act x ≫ e.hom = e.hom ≫ d'.E₁.act x := eact x
    simp only [Θ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [reassoc_of% (d.hact x), reassoc_of% h₂, h₃]
  · intro T t P
    let P₁ : SchemeHomOver t d.E₁.f := mapPt d.e.hom d.he P
    let P₂ : SchemeHomOver t d'.E₁.f := mapPt e.hom he₂ P₁
    have c1 : FactorsThrough d.K.levK P₁ ↔
        FactorsThrough d.K.levK (t := t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)))
          ⟨P₂.1 ≫ e.inv, by rw [Category.assoc, hvia.1.w, ← Category.assoc, P₂.2]⟩ :=
      factorsThrough_congr _ _ _ (by simp only [P₂, P₁, mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id])
    have c2 : FactorsThrough d'.K.levK P₂ ↔ FactorsThrough d'.K.levK (mapPt d'.e.hom d'.he (mapPt Θ.hom hΘ P)) :=
      factorsThrough_congr _ _ _ (by
        simp only [P₂, P₁, mapPt_coe, Θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    rw [d.hlev t P, c1, ← hK'' _ P₂, hKK t P₂, c2, ← d'.hlev t]
  · apply Subtype.ext
    have p1 := congrArg Subtype.val d.hP₁
    have p2 := congrArg Subtype.val eP
    have p3 := congrArg Subtype.val d'.hP₁
    simp only [mapPt_coe] at p1 p2 p3
    rw [hΘ₁, ← reassoc_of% p1]
    change (d.P₁.P).1 ≫ e.hom ≫ d'.e.inv = (w'.2.P).1
    rw [reassoc_of% p2]
    change (d'.P₁.P).1 ≫ d'.e.inv = (w'.2.P).1
    rw [p3, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end InjLaw

section SurjLaw

variable {S : Type} [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
  (x : Spec (CommRingCat.of S) ⟶ M N hM₁ hN hm' hloc)
  (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (ht₁ : (ptF₁ S s u).1 = x ≫ fM N hM₁ hN hm' hloc)

noncomputable abbrev ιM (U : M₁.affineOpens) : (datum N hM₁ hN hm' hloc U).Z ⟶ M N hM₁ hN hm' hloc :=
  (gluingData N hM₁ hN hm' hloc).cover.f U

theorem ιM_eq (U : M₁.affineOpens) : ιM N hM₁ hN hm' hloc U = colimit.ι (gluingData N hM₁ hN hm' hloc).functor U := rfl

theorem ιM_isOpenImmersion (U : M₁.affineOpens) : IsOpenImmersion (ιM N hM₁ hN hm' hloc U) :=
  (gluingData N hM₁ hN hm' hloc).cover.map_prop U

noncomputable def liftW (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) :
    (p.1.1 : (Spec (CommRingCat.of S)).Opens).toScheme ⟶ (datum N hM₁ hN hm' hloc p.1.2).Z :=
  haveI := ιM_isOpenImmersion N hM₁ hN hm' hloc p.1.2
  IsOpenImmersion.lift (ιM N hM₁ hN hm' hloc p.1.2)
    ((p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ x) (by
      rintro _ ⟨y, rfl⟩
      have hmem : ((p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ x) y ∈
          (gluingData N hM₁ hN hm' hloc).toBase ⁻¹' Set.range (M₁.directedAffineCover.f p.1.2) := by
        rw [Set.mem_preimage, Scheme.directedAffineCover_f]
        have hy : (x ≫ fM N hM₁ hN hm' hloc) y.1 ∈ (p.1.2 : M₁.Opens) := p.2 y.2
        refine ⟨⟨_, hy⟩, ?_⟩
        simp only [Scheme.Opens.ι_apply, Scheme.Hom.comp_apply]
        rfl
      rw [Scheme.Cover.RelativeGluingData.preimage_toBase_eq_range_ι] at hmem
      exact hmem)

theorem liftW_fac (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) :
    liftW N hM₁ hN hm' hloc x p ≫ ιM N hM₁ hN hm' hloc p.1.2 = (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ x :=
  haveI := ιM_isOpenImmersion N hM₁ hN hm' hloc p.1.2
  IsOpenImmersion.lift_fac _ _ _

theorem liftW_ζ (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) :
    liftW N hM₁ hN hm' hloc x p ≫ (datum N hM₁ hN hm' hloc p.1.2).ζ = cmap (x ≫ fM N hM₁ hN hm' hloc) p ≫ p.1.2.2.isoSpec.hom := by
  have sq := ((gluingData N hM₁ hN hm' hloc).isPullback_natTrans_ι_toBase p.1.2).w

  have key : liftW N hM₁ hN hm' hloc x p ≫ ((datum N hM₁ hN hm' hloc p.1.2).ζ ≫ p.1.2.2.isoSpec.inv) =
      cmap (x ≫ fM N hM₁ hN hm' hloc) p := by
    rw [← cancel_mono (p.1.2 : M₁.Opens).ι]
    simp only [cmap, Scheme.Hom.resLE_comp_ι, Category.assoc]
    have := congrArg (fun k => liftW N hM₁ hN hm' hloc x p ≫ k) sq
    try simp only [Category.assoc] at this
    refine this.trans ?_
    change liftW N hM₁ hN hm' hloc x p ≫ ιM N hM₁ hN hm' hloc p.1.2 ≫ fM N hM₁ hN hm' hloc = _
    rw [← Category.assoc, liftW_fac, Category.assoc]
  rw [← cancel_mono p.1.2.2.isoSpec.inv]
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using key

noncomputable def zW (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (φW (x ≫ fM N hM₁ hN hm' hloc) p))) (datum N hM₁ hN hm' hloc p.1.2).ζ :=
  ⟨p.1.1.2.isoSpec.inv ≫ liftW N hM₁ hN hm' hloc x p, by rw [Category.assoc, liftW_ζ, spec_φW]⟩

include ht₁ in
theorem exists_KW' (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) :
    ∃ K : (uW (x ≫ fM N hM₁ hN hm' hloc) u p).1.ExtraLevel N,
      (datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring _ p) (φW _ p) (uW _ u p)
        (uW_isPullback_uof hM₁ _ s u ht₁ p) K = zW N hM₁ hN hm' hloc x p :=
  (datum N hM₁ hN hm' hloc p.1.2).represents.2.2.1 (Wring _ p) (φW _ p) (uW _ u p)
    (uW_isPullback_uof hM₁ _ s u ht₁ p) (zW N hM₁ hN hm' hloc x p)

noncomputable def Kx (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) : (uW (x ≫ fM N hM₁ hN hm' hloc) u p).1.ExtraLevel N :=
  (exists_KW' N hM₁ hN hm' hloc s x u ht₁ p).choose

theorem Kx_spec (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) :
    (datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring _ p) (φW _ p) (uW _ u p)
      (uW_isPullback_uof hM₁ _ s u ht₁ p) (Kx N hM₁ hN hm' hloc s x u ht₁ p) = zW N hM₁ hN hm' hloc x p :=
  (exists_KW' N hM₁ hN hm' hloc s x u ht₁ p).choose_spec

noncomputable def gpq {t₁ : Spec (CommRingCat.of S) ⟶ M₁} (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)
    {p q : SecIdx t₁} (h : p ≤ q) : (uW t₁ u p).1.A ⟶ (uW t₁ u q).1.A :=
  (exists_gpq t₁ u h).choose

theorem gpq_spec {t₁ : Spec (CommRingCat.of S) ⟶ M₁} (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)
    {p q : SecIdx t₁} (h : p ≤ q) :
    gpq u h ≫ gW t₁ u q = gW t₁ u p ∧
      FakeEllipticCurve.IsPullbackVia (ρW _ h) (uW t₁ u q).1 (uW t₁ u p).1 (gpq u h) ∧
      ((uW t₁ u p).2.P).1 ≫ gpq u h = Spec.map (CommRingCat.ofHom (ρW _ h)) ≫ ((uW t₁ u q).2.P).1 :=
  (exists_gpq t₁ u h).choose_spec

theorem liftW_transZ {k i : SecIdx (x ≫ fM N hM₁ hN hm' hloc)} (h : k ≤ i) :
    liftW N hM₁ hN hm' hloc x k ≫ transZ N hM₁ hN hm' hloc h.2 =
      (Spec (CommRingCat.of S)).homOfLE h.1 ≫ liftW N hM₁ hN hm' hloc x i := by
  haveI := ιM_isOpenImmersion N hM₁ hN hm' hloc i.1.2
  rw [← cancel_mono (ιM N hM₁ hN hm' hloc i.1.2), Category.assoc, Category.assoc, liftW_fac]
  have hU : (k.1.2 : M₁.directedAffineCover.I₀) ⟶ i.1.2 := homOfLE h.2
  have hw : transZ N hM₁ hN hm' hloc h.2 ≫ ιM N hM₁ hN hm' hloc i.1.2 = ιM N hM₁ hN hm' hloc k.1.2 :=
    colimit.w (gluingData N hM₁ hN hm' hloc).functor hU
  rw [hw, liftW_fac, ← Category.assoc, Scheme.homOfLE_ι]

include ht₁ in

theorem Kx_iff_of_le {k i : SecIdx (x ≫ fM N hM₁ hN hm' hloc)} (h : k ≤ i)
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of (Wring _ k))) (R : SchemeHomOver t (uW _ u k).1.f) :
    FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ k).levK R ↔
      FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ i).levK (t := t ≫ Spec.map (CommRingCat.ofHom (ρW _ h)))
        ⟨R.1 ≫ gpq u h, by rw [Category.assoc, (gpq_spec u h).2.1.1.w, ← Category.assoc, R.2]⟩ := by
  obtain ⟨hcomp, hvia, hP⟩ := gpq_spec u h
  obtain ⟨Kt, hKt⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (ρW _ h) _ _ (gpq u h) hvia N (Kx N hM₁ hN hm' hloc s x u ht₁ i)
  rw [← hKt t R]

  have hWq : FakeEllipticCurve.WithFullLevel.IsPullback (ρW _ h) (uW _ u i) (uW _ u k) := by
    obtain ⟨hg, hm, ha, hl⟩ := hvia; exact ⟨gpq u h, hg, hm, ha, hl, hP⟩
  have hu'' : FakeEllipticCurve.WithFullLevel.IsPullback ((ρW _ h).comp (φW _ i)) (uof hM₁ i.1.2) (uW _ u k) :=
    isPullback_comp _ _ _ _ _ (uW_isPullback_uof hM₁ _ s u ht₁ i) hWq
  have law2 := (datum N hM₁ hN hm' hloc i.1.2).represents.2.1 (Wring _ i) (Wring _ k) (φW _ i) (ρW _ h)
    (uW _ u i) (uW _ u k) (uW_isPullback_uof hM₁ _ s u ht₁ i) hu'' (Kx N hM₁ hN hm' hloc s x u ht₁ i) Kt (gpq u h)
    hvia hP (fun t P hP => (hKt t P).mp hP)
  rw [Kx_spec] at law2
  have hu₃ : FakeEllipticCurve.WithFullLevel.IsPullback ((φW _ k).comp (resRing h.2)) (uof hM₁ i.1.2) (uW _ u k) :=
    isPullback_comp _ _ _ _ _ (uof_isPullback hM₁ h.2) (uW_isPullback_uof hM₁ _ s u ht₁ k)
  have ht := (transZ_spec N hM₁ hN hm' hloc h.2).2 (Wring _ k) (φW _ k) (uW _ u k)
    (uW_isPullback_uof hM₁ _ s u ht₁ k) hu₃ (Kx N hM₁ hN hm' hloc s x u ht₁ k)
  rw [Kx_spec] at ht

  have e1 : (zW N hM₁ hN hm' hloc x k).1 ≫ transZ N hM₁ hN hm' hloc h.2 =
      Spec.map (CommRingCat.ofHom (ρW _ h)) ≫ (zW N hM₁ hN hm' hloc x i).1 := by
    change (k.1.1.2.isoSpec.inv ≫ liftW N hM₁ hN hm' hloc x k) ≫ _ = _ ≫ (i.1.1.2.isoSpec.inv ≫ liftW N hM₁ hN hm' hloc x i)
    rw [Category.assoc, liftW_transZ N hM₁ hN hm' hloc x h, ← Category.assoc, ← Category.assoc, spec_ρW]
  have key : (datum N hM₁ hN hm' hloc i.1.2).ptZ (Wring _ k) ((ρW _ h).comp (φW _ i)) (uW _ u k) hu''
      (Kx N hM₁ hN hm' hloc s x u ht₁ k) =
      (datum N hM₁ hN hm' hloc i.1.2).ptZ (Wring _ k) ((ρW _ h).comp (φW _ i)) (uW _ u k) hu'' Kt := by
    apply Subtype.ext
    dsimp only at ht
    rw [law2, ← e1, ht]
    exact (datum N hM₁ hN hm' hloc i.1.2).ptZ_congr N (ρW_comp_φW _ h) _ _ _ _
  exact (datum N hM₁ hN hm' hloc i.1.2).represents.2.2.2 _ _ _ _ _ _ key t R

omit hM₁ in
theorem b_eq {t₁ : Spec (CommRingCat.of S) ⟶ M₁} (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (i : SecIdx t₁)
    {T : Scheme.{0}} (tᵢ : T ⟶ Spec (CommRingCat.of (Wring t₁ i))) (Pᵢ : SchemeHomOver tᵢ (uW t₁ u i).1.f) :
    Pᵢ.1 ≫ gW t₁ u i ≫ u.1.f = tᵢ ≫ Wι t₁ i := by
  rw [(gW_via t₁ u i).1.1.w, ← Category.assoc, Pᵢ.2, spec_rW]

include ht₁ in

theorem Kx_compat_dir (i j : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) {T : Scheme.{0}}
    (tᵢ : T ⟶ Spec (CommRingCat.of (Wring _ i))) (tⱼ : T ⟶ Spec (CommRingCat.of (Wring _ j)))
    (Pᵢ : SchemeHomOver tᵢ (uW _ u i).1.f) (Pⱼ : SchemeHomOver tⱼ (uW _ u j).1.f)
    (hP : Pᵢ.1 ≫ gW _ u i = Pⱼ.1 ≫ gW _ u j)
    (hPi : FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ i).levK Pᵢ) :
    FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ j).levK Pⱼ := by
  let b : T ⟶ Spec (CommRingCat.of S) := Pᵢ.1 ≫ gW (x ≫ fM N hM₁ hN hm' hloc) u i ≫ u.1.f
  have hbi : b = tᵢ ≫ Wι (x ≫ fM N hM₁ hN hm' hloc) i := b_eq u i tᵢ Pᵢ
  have hbj : b = tⱼ ≫ Wι (x ≫ fM N hM₁ hN hm' hloc) j := by rw [← b_eq u j tⱼ Pⱼ, ← reassoc_of% hP]

  let J : Type := {k : SecIdx (x ≫ fM N hM₁ hN hm' hloc) // k ≤ i ∧ k ≤ j}
  have hcov : ∀ y : T, ∃ (k : J) (z : ↥(pullback b ((k.1.1.1 : (Spec (CommRingCat.of S)).Opens).ι))),
      pullback.fst b _ z = y := by
    intro y
    have hyi : b y ∈ (i.1.1 : (Spec (CommRingCat.of S)).Opens) := by
      rw [hbi, Scheme.Hom.comp_apply, Wι, Scheme.Hom.comp_apply]; exact (i.1.1.2.isoSpec.inv (tᵢ y)).2
    have hyj : b y ∈ (j.1.1 : (Spec (CommRingCat.of S)).Opens) := by
      rw [hbj, Scheme.Hom.comp_apply, Wι, Scheme.Hom.comp_apply]; exact (j.1.1.2.isoSpec.inv (tⱼ y)).2
    obtain ⟨k, hyk, hkW, hkU⟩ := exists_secIdx (x ≫ fM N hM₁ hN hm' hloc) (b y) ((i.1.1 : (Spec (CommRingCat.of S)).Opens) ⊓ j.1.1) ⟨hyi, hyj⟩
      ((i.1.2 : M₁.Opens) ⊓ j.1.2) ⟨i.2 hyi, j.2 hyj⟩
    have hy : y ∈ Set.range (pullback.fst b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι)) := by
      rw [Scheme.Pullback.range_fst]
      show b y ∈ Set.range _
      rw [Scheme.Opens.range_ι]; exact hyk
    obtain ⟨z, hz⟩ := hy
    exact ⟨⟨k, ⟨fun w hw => (hkW hw).1, fun w hw => (hkU hw).1⟩, ⟨fun w hw => (hkW hw).2, fun w hw => (hkU hw).2⟩⟩, z, hz⟩
  let 𝒯 : T.OpenCover := Scheme.Cover.mkOfCovers J (fun k => pullback b ((k.1.1.1 : (Spec (CommRingCat.of S)).Opens).ι))
    (fun k => pullback.fst b _) hcov
  haveI := (Kx N hM₁ hN hm' hloc s x u ht₁ j).levK_closed
  apply factorsThrough_of_openCover (Kx N hM₁ hN hm' hloc s x u ht₁ j).levK Pⱼ.1 𝒯
  rintro ⟨k, hki, hkj⟩
  change ∃ l, l ≫ _ = pullback.fst b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ≫ Pⱼ.1

  let tk : pullback b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ⟶ Spec (CommRingCat.of (Wring (x ≫ fM N hM₁ hN hm' hloc) k)) :=
    pullback.snd b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ≫ k.1.1.2.isoSpec.hom
  have htk : tk ≫ Wι (x ≫ fM N hM₁ hN hm' hloc) k = pullback.fst b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ≫ b := by
    simp only [tk, Wι, Category.assoc]
    erw [Iso.hom_inv_id_assoc]
    exact (pullback.condition (f := b) (g := (k.1.1 : (Spec (CommRingCat.of S)).Opens).ι)).symm
  have hsq := (gW_via (x ≫ fM N hM₁ hN hm' hloc) u k).1.1
  let Q : pullback b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ⟶ (uW (x ≫ fM N hM₁ hN hm' hloc) u k).1.A :=
    hsq.lift (pullback.fst b _ ≫ Pᵢ.1 ≫ gW (x ≫ fM N hM₁ hN hm' hloc) u i) tk (by rw [spec_rW, htk]; simp only [b, Category.assoc])
  have hQ₁ : Q ≫ gW (x ≫ fM N hM₁ hN hm' hloc) u k = pullback.fst b _ ≫ Pᵢ.1 ≫ gW (x ≫ fM N hM₁ hN hm' hloc) u i := hsq.lift_fst _ _ _
  have hQ₂ : Q ≫ (uW (x ≫ fM N hM₁ hN hm' hloc) u k).1.f = tk := hsq.lift_snd _ _ _

  have cmp : ∀ (l : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) (hkl : k ≤ l) (tl : T ⟶ Spec (CommRingCat.of (Wring (x ≫ fM N hM₁ hN hm' hloc) l))) (Pl : SchemeHomOver tl (uW (x ≫ fM N hM₁ hN hm' hloc) u l).1.f)
      (hbl : b = tl ≫ Wι (x ≫ fM N hM₁ hN hm' hloc) l) (hQl : Q ≫ gW (x ≫ fM N hM₁ hN hm' hloc) u k = pullback.fst b _ ≫ Pl.1 ≫ gW (x ≫ fM N hM₁ hN hm' hloc) u l),
      pullback.fst b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ≫ Pl.1 = Q ≫ gpq u hkl := by
    intro l hkl tl Pl hbl hQl
    obtain ⟨hcomp, hvia, -⟩ := gpq_spec u hkl
    apply (gW_via (x ≫ fM N hM₁ hN hm' hloc) u l).1.1.hom_ext
    · rw [Category.assoc, Category.assoc, hcomp, hQl]
    · have aux : pullback.fst b ((k.1.1 : (Spec (CommRingCat.of S)).Opens).ι) ≫ tl =
          tk ≫ Spec.map (CommRingCat.ofHom (ρW (x ≫ fM N hM₁ hN hm' hloc) hkl)) := by
        haveI : Mono (Wι (x ≫ fM N hM₁ hN hm' hloc) l) := by unfold Wι; infer_instance
        rw [← cancel_mono (Wι (x ≫ fM N hM₁ hN hm' hloc) l), Category.assoc, Category.assoc, ← hbl, ← htk]
        simp only [Wι]
        rw [← Category.assoc (Spec.map _), spec_ρW]
        simp only [Category.assoc, tk, Scheme.homOfLE_ι]
      rw [Category.assoc, Category.assoc, hvia.1.w, ← Category.assoc Q, hQ₂, Pl.2, aux]
  have ei := cmp i hki tᵢ Pᵢ hbi hQ₁
  have ej := cmp j hkj tⱼ Pⱼ hbj (by rw [hQ₁, hP])
  have r2 : FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ k).levK ⟨Q, hQ₂⟩ := by
    refine (Kx_iff_of_le N hM₁ hN hm' hloc s x u ht₁ hki tk ⟨Q, hQ₂⟩).mpr ?_
    obtain ⟨P₀, hP₀⟩ := hPi
    exact ⟨pullback.fst b _ ≫ P₀, by rw [Category.assoc, hP₀, ei]⟩
  obtain ⟨l, hl⟩ := (Kx_iff_of_le N hM₁ hN hm' hloc s x u ht₁ hkj tk ⟨Q, hQ₂⟩).mp r2
  exact ⟨l, hl.trans ej.symm⟩

include ht₁ in

theorem exists_K₀ : ∃ K₀ : u.1.ExtraLevel N, ∀ (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of (Wring _ p))) (P : SchemeHomOver t (uW _ u p).1.f),
      FactorsThrough K₀.levK (t := t ≫ Spec.map (CommRingCat.ofHom (rW _ p)))
        ⟨P.1 ≫ gW _ u p, by rw [Category.assoc, (gW_via _ u p).1.1.w, ← Category.assoc, P.2]⟩ ↔
      FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ p).levK P := by
  obtain ⟨K₀, hK₀, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover
    u.1 N (fun p : SecIdx (x ≫ fM N hM₁ hN hm' hloc) => Wring _ p) (fun p => rW _ p) (fun p => inferInstance)
    (fun y => by
      obtain ⟨p, hy, -, -⟩ := exists_secIdx (x ≫ fM N hM₁ hN hm' hloc) y ⊤ trivial ⊤ trivial
      refine ⟨p, p.1.1.2.isoSpec.hom ⟨y, hy⟩, ?_⟩
      rw [spec_rW, ← Scheme.Hom.comp_apply, Wι, Iso.hom_inv_id_assoc]
      rfl)
    (fun p => (uW _ u p).1) (fun p => gW _ u p) (fun p => (gW_via _ u p).1.1) (fun p => (gW_via _ u p).1.2.1)
    (fun p => (gW_via _ u p).1.2.2.1)
    (fun p {T} t P h => hlev'_level_one (rW _ p) u.1 (uW _ u p).1 (gW _ u p) (gW_via _ u p).1 t P h)
    (fun p => Kx N hM₁ hN hm' hloc s x u ht₁ p)
    (fun i j {T} tᵢ tⱼ Pᵢ Pⱼ hP =>
      ⟨Kx_compat_dir N hM₁ hN hm' hloc s x u ht₁ i j tᵢ tⱼ Pᵢ Pⱼ hP,
       Kx_compat_dir N hM₁ hN hm' hloc s x u ht₁ j i tⱼ tᵢ Pⱼ Pᵢ hP.symm⟩)
  exact ⟨K₀, hK₀⟩

include ht₁ in

theorem secOf_eq_x (K₀ : u.1.ExtraLevel N)
    (hK₀ : ∀ (p : SecIdx (x ≫ fM N hM₁ hN hm' hloc)) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of (Wring _ p))) (P : SchemeHomOver t (uW _ u p).1.f),
      FactorsThrough K₀.levK (t := t ≫ Spec.map (CommRingCat.ofHom (rW _ p)))
        ⟨P.1 ≫ gW _ u p, by rw [Category.assoc, (gW_via _ u p).1.1.w, ← Category.assoc, P.2]⟩ ↔
      FactorsThrough (Kx N hM₁ hN hm' hloc s x u ht₁ p).levK P) :
    secOf N hM₁ hN hm' hloc (x ≫ fM N hM₁ hN hm' hloc) s u ht₁ K₀ = x := by
  apply (secCover (x ≫ fM N hM₁ hN hm' hloc)).hom_ext
  intro p
  change (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ _ = (p.1.1 : (Spec (CommRingCat.of S)).Opens).ι ≫ x
  rw [ι_secOf]
  have e1 : (datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring _ p) (φW _ p) (uW _ u p) (uW_isPullback_uof hM₁ _ s u ht₁ p)
      (KW N _ u K₀ p) = zW N hM₁ hN hm' hloc x p := by
    rw [← Kx_spec N hM₁ hN hm' hloc s x u ht₁ p]
    exact (datum N hM₁ hN hm' hloc p.1.2).represents.1 _ _ _ _ _ _ fun t Q =>
      (KW_spec N _ u K₀ p t Q).trans (hK₀ p t Q)
  change p.1.1.2.isoSpec.hom ≫ ((datum N hM₁ hN hm' hloc p.1.2).ptZ (Wring _ p) (φW _ p) (uW _ u p)
    (uW_isPullback_uof hM₁ _ s u ht₁ p) (KW N _ u K₀ p)).1 ≫ colimit.ι (gluingData N hM₁ hN hm' hloc).functor p.1.2 = _
  rw [e1, ← ιM_eq, ← liftW_fac N hM₁ hN hm' hloc x p]
  change p.1.1.2.isoSpec.hom ≫ (p.1.1.2.isoSpec.inv ≫ liftW N hM₁ hN hm' hloc x p) ≫ _ = _
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc]

include hM₁ hN hm' hloc ht₁ in

theorem exists_w_of_K₀ (K₀ : u.1.ExtraLevel N) (hx : secOf N hM₁ hN hm' hloc (x ≫ fM N hM₁ hN hm' hloc) s u ht₁ K₀ = x) :
    ∃ w : FakeEllipticCurve.WithFullLevel Λ N m S, (ptFM N hM₁ hN hm' hloc s w).1 = x := by
  obtain ⟨E, e, he, hmul, hact, hlev⟩ :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelOne_extraLevel_and_exists_of_extraLevel Λ N S).2 u.1 K₀
  have he' : e.inv ≫ E.f = u.1.f := by rw [← he, Iso.inv_hom_id_assoc]
  have hmul' := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f) =>
    mapPt_inv_mul E u.1 e he he' hmul t P Q
  have hact' : ∀ y : ↥Λ, u.1.act y ≫ e.inv = e.inv ≫ E.act y := by
    intro y
    rw [← cancel_epi e.hom, ← Category.assoc, ← hact y, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  obtain ⟨PE, hPE⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt u.1 E e.symm he' hmul' hact' u.2
  let w : FakeEllipticCurve.WithFullLevel Λ N m S := ⟨E, PE⟩
  refine ⟨w, ?_⟩
  set d := lev1Data N w

  let G : u.1.A ⟶ d.E₁.A := e.inv ≫ d.e.hom
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have hGf : G ≫ d.E₁.f = u.1.f := by simp only [G, Category.assoc, d.he]; exact he'
  have sq : IsPullback G u.1.f d.E₁.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [hid]; exact IsPullback.of_horiz_isIso ⟨by rw [hGf, Category.comp_id]⟩
  have hmulG : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      (u.1.L.mul t P Q).1 ≫ G =
        (d.E₁.L.mul (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)))
          ⟨P.1 ≫ G, by rw [Category.assoc, sq.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ G, by rw [Category.assoc, sq.w, ← Category.assoc, Q.2]⟩).1 := by
    intro X t P Q
    have h1 := congrArg Subtype.val (hmul' t P Q)
    have h2 := fun (A B : SchemeHomOver t E.f) => congrArg Subtype.val (d.hmul t A B)
    simp only [mapPt_coe] at h1 h2
    simp only [G, ← Category.assoc]
    rw [h1]
    erw [h2]
    exact mul_val_congr d.E₁.L (by rw [hid, Category.comp_id]) _ _ _ _ (by simp [mapPt_coe, Category.assoc])
      (by simp [mapPt_coe, Category.assoc])
  have hvia : FakeEllipticCurve.IsPullbackVia (RingHom.id S) (lev1 N w).1 u.1 G := by
    refine ⟨sq, hmulG, ?_, lev_to_lev_level_one (RingHom.id S) d.E₁ u.1 G sq hmulG⟩
    intro y
    simp only [G]
    rw [← Category.assoc, hact' y, Category.assoc, d.hact y, Category.assoc]
  have hGP : (u.2.P).1 ≫ G = Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ ((lev1 N w).2.P).1 := by
    rw [hid, Category.id_comp]
    show (u.2.P).1 ≫ (e.inv ≫ d.e.hom) = (d.P₁.P).1
    rw [d.hP₁, mapPt_coe, show w.2.P = PE.P from rfl, hPE, mapPt_coe]
    simp only [Iso.symm_hom, Category.assoc]
  have hKK' : ∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t' u.1.f),
      FactorsThrough K₀.levK P → ∃ P₀ : X ⟶ d.K.K, P₀ ≫ d.K.levK = P.1 ≫ G := by
    intro X t' P hP
    have c : FactorsThrough K₀.levK P ↔ FactorsThrough K₀.levK (mapPt e.hom he (mapPt e.inv he' P)) :=
      factorsThrough_congr _ _ _ (by simp [mapPt_coe])
    have hE := (hlev t' (mapPt e.inv he' P)).mpr (c.mp hP)
    obtain ⟨P₀, hP₀⟩ := (d.hlev t' (mapPt e.inv he' P)).mp hE
    exact ⟨P₀, by rw [hP₀]; simp only [mapPt_coe, G, Category.assoc]⟩
  have key := secOf_pullback N hM₁ hN hm' hloc (RingHom.id S) s s (by rw [hid, Category.id_comp]) (lev1 N w) u G hvia hGP
    d.K K₀ hKK' rfl ht₁
  rw [hid, Category.id_comp, hx] at key
  exact key.symm

include hM₁ hN hm' hloc in
theorem ptFM_surjective' (x' : SchemeHomOver s (fM N hM₁ hN hm' hloc ≫ π₁)) :
    ∃ w : FakeEllipticCurve.WithFullLevel Λ N m S, ptFM N hM₁ hN hm' hloc s w = x' := by
  obtain ⟨u', hu'⟩ := hM₁.ptF_surjective S s ⟨x'.1 ≫ fM N hM₁ hN hm' hloc, by rw [Category.assoc]; exact x'.2⟩
  have ht₁' : (ptF₁ S s u').1 = x'.1 ≫ fM N hM₁ hN hm' hloc := congrArg Subtype.val hu'
  obtain ⟨K₀, hK₀⟩ := exists_K₀ N hM₁ hN hm' hloc s x'.1 u' ht₁'
  have hx := secOf_eq_x N hM₁ hN hm' hloc s x'.1 u' ht₁' K₀ hK₀
  obtain ⟨w, hw⟩ := exists_w_of_K₀ N hM₁ hN hm' hloc s x'.1 u' ht₁' K₀ hx
  exact ⟨w, Subtype.ext hw⟩

end SurjLaw

section Laws

include hM₁ hN hm' hloc in
theorem ptFM_iso (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (w w' : FakeEllipticCurve.WithFullLevel Λ N m S) (h : FakeEllipticCurve.WithFullLevel.Iso w w') :
    ptFM N hM₁ hN hm' hloc s w = ptFM N hM₁ hN hm' hloc s w' :=
  ptFM_iso' N hM₁ hN hm' hloc S s w w' h

include hM₁ hN hm' hloc in
theorem ptFM_pullback (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪))
    (hs : Spec.map (CommRingCat.ofHom φ) ≫ s = s')
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (w' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ w w') :
    (ptFM N hM₁ hN hm' hloc s' w').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptFM N hM₁ hN hm' hloc s w).1 :=
  ptFM_pullback' N hM₁ hN hm' hloc S S' φ s s' hs w w' h

include hM₁ hN hm' hloc in
theorem ptFM_surjective (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (x : SchemeHomOver s (fM N hM₁ hN hm' hloc ≫ π₁)) :
    ∃ w : FakeEllipticCurve.WithFullLevel Λ N m S, ptFM N hM₁ hN hm' hloc s w = x :=
  ptFM_surjective' N hM₁ hN hm' hloc s x

include hM₁ hN hm' hloc in
theorem ptFM_injective (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (w w' : FakeEllipticCurve.WithFullLevel Λ N m S) (h : ptFM N hM₁ hN hm' hloc s w = ptFM N hM₁ hN hm' hloc s w') :
    FakeEllipticCurve.WithFullLevel.Iso w w' :=
  ptFM_injective' N hM₁ hN hm' hloc S s w w' h

end Laws

end Glue

end BodyL2
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_forall_local_via.BodyL2"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M₁ : Scheme.{0}} {π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁}
    (hM₁ : IsFineModuli Λ 1 m M₁ π₁ ptF₁)
    (hloc : ∀ (S : Type) [CommRing S], IsUnit ((N : ℕ) : S) → IsUnit ((m : ℕ) : S) → ∀ u : FakeEllipticCurve.WithFullLevel Λ 1 m S,
      ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
        (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (K K' : u'.1.ExtraLevel N),
            (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) → ptZ T φ u' hu' K = ptZ T φ u' hu' K') ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
            (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T) (u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T')
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (hu'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'')
            (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) (g : u''.1.A ⟶ u'.1.A),

            FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g →
            (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
            (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
              FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) →
              (ptZ T' (ψ.comp φ) u'' hu'' K'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ u' hu' K').1) ∧

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ), ∃ K : u'.1.ExtraLevel N, ptZ T φ u' hu' K = z) ∧
        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (K K' : u'.1.ExtraLevel N), ptZ T φ u' hu' K = ptZ T φ u' hu' K' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P)) :
    ∃ (M : Scheme.{0}) (f : M ⟶ M₁)
      (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s (f ≫ π₁)),
      IsFineModuli Λ N m M (f ≫ π₁) ptF ∧ IsFinite f ∧ Etale f := by
  have hloc' : ∀ (S : Type) [CommRing S], IsUnit ((N : ℕ) : S) → IsUnit ((m : ℕ) : S) →
      ∀ u : FakeEllipticCurve.WithFullLevel Λ 1 m S,
        ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
          (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
            FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N →
              SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
          BodyL2.RepresentsExtraLevel Λ N m u ζ ptZ := hloc
  refine ⟨BodyL2.M N hM₁ hN hm' hloc', BodyL2.fM N hM₁ hN hm' hloc', fun S _ s w => BodyL2.ptFM N hM₁ hN hm' hloc' s w,
    ⟨BodyL2.ptFM_iso N hM₁ hN hm' hloc', BodyL2.ptFM_pullback N hM₁ hN hm' hloc', BodyL2.ptFM_surjective N hM₁ hN hm' hloc',
      BodyL2.ptFM_injective N hM₁ hN hm' hloc'⟩,
    BodyL2.isFinite_fM N hM₁ hN hm' hloc', BodyL2.etale_fM N hM₁ hN hm' hloc'⟩

end S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_forall_local_via
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_forall_local_via (solution)
