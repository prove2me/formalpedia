-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.existsUnique_hom_isPullback_of_represents_extraLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b6b80b2f-426c-59f5-a8b4-f303fca7d1be

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_mapPt_iff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_levK_of_exists_comp_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "WithFullLevel WithFullLevel.IsPullback ExtraLevel WithExtraLevel IsPullback A f act lev_torsion L lev_one C lev IsPullbackVia WithFullLevel.exists_isPullback IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq WithExtraLevel.exists_isPullback exists_extraLevel_forall_factorsThrough_mapPt_iff factorsThrough_levK_of_exists_comp_eq_of_isPullback"
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

section OneG

theorem RGL_eq_one_of_mul_self {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (h : L.mul t x x = x) : x = L.one t :=
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.inv_mul_cancel]

theorem RGL_mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)}
    (e : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst e
  have h1 : x₁ = x₂ := Subtype.ext hx
  have h2 : y₁ = y₂ := Subtype.ext hy
  subst h1 h2
  rfl

theorem factorsThrough_lev_iff_eq_one_of_level_one' {S : Type} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough E.lev P ↔ P = E.L.one t := by
  constructor
  · intro h
    have h1 := E.lev_torsion t P h
    change E.L.mul t (E.L.one t) P = E.L.one t at h1
    rwa [E.L.one_mul] at h1
  · rintro rfl
    exact E.lev_one t

theorem one_comp_of_isPullbackVia {N : ℕ} {T₀ T : Type} [CommRing T₀] [CommRing T] (ψ : T₀ →+* T)
    (E₀ : FakeEllipticCurve Λ N T₀) (E' : FakeEllipticCurve Λ N T) (g' : E'.A ⟶ E₀.A) (h' : IsPullbackVia ψ E₀ E' g')
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) :
    (E'.L.one t).1 ≫ g' = (E₀.L.one (t ≫ Spec.map (CommRingCat.ofHom ψ))).1 := by
  obtain ⟨hg, hmul, -, -⟩ := h'
  have h := hmul t (E'.L.one t) (E'.L.one t)
  rw [E'.L.one_mul] at h

  have := RGL_eq_one_of_mul_self E₀.L (t ≫ Spec.map (CommRingCat.ofHom ψ))
    ⟨(E'.L.one t).1 ≫ g', by rw [Category.assoc, hg.w, ← Category.assoc, (E'.L.one t).2]⟩ (Subtype.ext h.symm)
  exact congrArg Subtype.val this

theorem hlev_of_level_one {T₀ T : Type} [CommRing T₀] [CommRing T] (ψ : T₀ →+* T)
    (E₀ : FakeEllipticCurve Λ 1 T₀) (E' : FakeEllipticCurve Λ 1 T) (g' : E'.A ⟶ E₀.A) (h' : IsPullbackVia ψ E₀ E' g')
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t E'.f)
    (hP : ∃ P₀ : X ⟶ E₀.C, P₀ ≫ E₀.lev = P.1 ≫ g') : FactorsThrough E'.lev P := by
  obtain ⟨hg, -⟩ := id h'
  rw [factorsThrough_lev_iff_eq_one_of_level_one']

  have h1 : (⟨P.1 ≫ g', by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ :
      SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom ψ)) E₀.f) = E₀.L.one _ :=
    (factorsThrough_lev_iff_eq_one_of_level_one' E₀ _ _).mp hP
  apply Subtype.ext
  apply hg.hom_ext
  · rw [one_comp_of_isPullbackVia ψ E₀ E' g' h' t]
    exact congrArg Subtype.val h1
  · rw [P.2, (E'.L.one t).2]

end OneG

section Compare

theorem exists_comparison_of_isPullbackVia {ℓ : ℕ} {T₀ T : Type} [CommRing T₀] [CommRing T] (ψ : T₀ →+* T)
    (E₀ : FakeEllipticCurve Λ 1 T₀) (E' E'' : FakeEllipticCurve Λ 1 T)
    (g' : E'.A ⟶ E₀.A) (g'' : E''.A ⟶ E₀.A)
    (h' : IsPullbackVia ψ E₀ E' g') (h'' : IsPullbackVia ψ E₀ E'' g'')
    (K'' : E''.ExtraLevel ℓ) :
    ∃ (k : E''.A ⟶ E'.A) (hk : k ≫ E'.f = E''.f), k ≫ g' = g'' ∧ IsIso k ∧
      FakeEllipticCurve.IsPullbackVia (RingHom.id T) E' E'' k ∧
      (∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t E''.f),
          mapPt k hk (E''.L.mul t P Q) = E'.L.mul t (mapPt k hk P) (mapPt k hk Q)) ∧
      (∀ x : ↥Λ, E''.act x ≫ k = k ≫ E'.act x) ∧
      ∃ K' : E'.ExtraLevel ℓ, ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t E''.f),
          FactorsThrough K'.levK (mapPt k hk P) ↔ FactorsThrough K''.levK P := by
  obtain ⟨k, hkg, hkf, -, hpb⟩ :=
    IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq ψ (RingHom.id T) ψ (RingHom.id_comp ψ) E₀ E' E'' g' h'
      (fun t P hP => hlev_of_level_one ψ E₀ E' g' h' t P hP) g'' h''
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id T)) = 𝟙 (Spec (CommRingCat.of T)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hk : k ≫ E'.f = E''.f := by rw [hkf, hid, Category.comp_id]
  obtain ⟨hgpb, hmulk, hactk, -⟩ := id hpb
  haveI hiso : IsIso k := hgpb.isIso_fst_of_isIso (by rw [hid]; infer_instance)
  have hmul : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t E''.f),
      mapPt k hk (E''.L.mul t P Q) = E'.L.mul t (mapPt k hk P) (mapPt k hk Q) := by
    intro X t P Q
    apply Subtype.ext
    change (E''.L.mul t P Q).1 ≫ k = (E'.L.mul t (mapPt k hk P) (mapPt k hk Q)).1
    rw [hmulk t P Q]
    exact RGL_mul_val_congr E'.L (by rw [hid, Category.comp_id]) _ _ _ _ rfl rfl
  have hone : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)), mapPt k hk (E''.L.one t) = E'.L.one t := by
    intro X t
    exact RGL_eq_one_of_mul_self E'.L t _ (by rw [← hmul, E''.L.one_mul])
  refine ⟨k, hk, hkg, hiso, hpb, hmul, hactk, ?_⟩
  have hlev : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t E''.f),
      FactorsThrough E''.lev P ↔ FactorsThrough E'.lev (mapPt (asIso k).hom hk P) := by
    intro X t P
    rw [factorsThrough_lev_iff_eq_one_of_level_one', factorsThrough_lev_iff_eq_one_of_level_one']
    change P = E''.L.one t ↔ mapPt k hk P = E'.L.one t
    constructor
    · rintro rfl; exact hone t
    · intro h
      rw [← hone t] at h
      apply Subtype.ext
      have h2 := congrArg Subtype.val h
      change P.1 ≫ k = (E''.L.one t).1 ≫ k at h2
      exact (cancel_mono k).mp h2
  obtain ⟨K', hK'⟩ := exists_extraLevel_forall_factorsThrough_mapPt_iff ℓ E'' E' (asIso k) hk hmul hactk hlev K''
  exact ⟨K', hK'⟩

end Compare

section OneGMain

namespace WithFullLevel p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel" "IsPullback exists_isPullback" end WithFullLevel
p2m_open_scoped "CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel" in

theorem WithFullLevel.exists_isPullbackVia_extraLevel {m ℓ : ℕ} {T T' : Type} [CommRing T] [CommRing T'] (χ : T →+* T')
    (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T) (K' : u'.1.ExtraLevel ℓ) :
    ∃ (u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T') (K'' : u''.1.ExtraLevel ℓ) (g : u''.1.A ⟶ u'.1.A),
      FakeEllipticCurve.WithFullLevel.IsPullback χ u' u'' ∧
      FakeEllipticCurve.IsPullbackVia χ u'.1 u''.1 g ∧
      (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom χ) ≫ (u'.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
          FactorsThrough K''.levK P ↔ ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) := by

  obtain ⟨u'', hu''⟩ := WithFullLevel.exists_isPullback χ u'
  obtain ⟨g, hg, hmul, hact, hlev, hgen⟩ := hu''
  have hvia : IsPullbackVia χ u'.1 u''.1 g := ⟨hg, hmul, hact, hlev⟩

  obtain ⟨w, hw⟩ := WithExtraLevel.exists_isPullback χ (⟨u'.1, K'⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 ℓ T)
  obtain ⟨g₂, hg₂, hmul₂, hact₂, hlev₂⟩ := hw
  have hvia₂ : IsPullbackVia χ u'.1 w.1 g₂ := ⟨hg₂, hmul₂, hact₂, fun t' P h => (hlev₂ t' P).1 h⟩

  obtain ⟨k, hk, hkg, hkiso, -, hkmul, hkact, K'', hK''⟩ :=
    exists_comparison_of_isPullbackVia χ u'.1 u''.1 w.1 g g₂ hvia hvia₂ w.2
  refine ⟨u'', K'', g, ⟨g, hg, hmul, hact, hlev, hgen⟩, hvia, hgen, ?_⟩
  intro T₀ t P

  have hkinv : inv k ≫ w.1.f = u''.1.f := by rw [← hk, IsIso.inv_hom_id_assoc]
  let Q : SchemeHomOver t w.1.f := mapPt (inv k) hkinv P
  have hQ : mapPt k hk Q = P := by
    apply Subtype.ext
    change (P.1 ≫ inv k) ≫ k = P.1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hQg : Q.1 ≫ g₂ = P.1 ≫ g := by
    change (P.1 ≫ inv k) ≫ g₂ = P.1 ≫ g
    rw [← hkg, Category.assoc, IsIso.inv_hom_id_assoc]
  have e1 : FactorsThrough K''.levK P ↔ FactorsThrough w.2.levK Q := by rw [← hQ]; exact hK'' t Q
  rw [e1, ← hQg]
  exact ⟨(hlev₂ t Q).2,
    factorsThrough_levK_of_exists_comp_eq_of_isPullback χ ⟨u'.1, K'⟩ w g₂ hg₂ (fun t' P' h => (hlev₂ t' P').2 h) t Q⟩

end OneGMain

end CerednikDrinfeld.QM.FakeEllipticCurve

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld.QM NeronModelInfra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace ZUniq
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

theorem specMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem specMap_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 (Spec (CommRingCat.of R)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem exists_eq_specMap {R S : Type} [CommRing R] [CommRing S]
    (z : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    ∃ ψ : R →+* S, Spec.map (CommRingCat.ofHom ψ) = z := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective z
  exact ⟨φ.hom, by rw [CommRingCat.ofHom_hom]⟩

theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  rwa [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at this

theorem mul_coe_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (e : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f)
    (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst e
  rw [show x₁ = x₂ from Subtype.ext hx, show y₁ = y₂ from Subtype.ext hy]

namespace WithFullLevel.IsPullback
private theorem _root_.CerednikDrinfeld.QM.ZUniq.WithFullLevel.IsPullback.trans {m : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    {φ : S →+* S'} {ψ : S' →+* S''} {u : FakeEllipticCurve.WithFullLevel Λ 1 m S}
    {u' : FakeEllipticCurve.WithFullLevel Λ 1 m S'} {u'' : FakeEllipticCurve.WithFullLevel Λ 1 m S''}
    (h : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
    (h' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u' u'') :
    FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'' := by
  obtain ⟨g, hg, hmul, hact, hlev, hgen⟩ := h
  obtain ⟨g', hg', hmul', hact', hlev', hgen'⟩ := h'
  have hsq : CategoryTheory.IsPullback (g' ≫ g) u''.1.f u.1.f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [specMap_comp]; exact hg'.paste_horiz hg
  refine ⟨g' ≫ g, hsq, fun t' P Q => ?_, fun x => ?_, fun t' P hP => ?_, ?_⟩
  · rw [← Category.assoc, hmul', hmul]
    exact mul_coe_congr u.1.L (by rw [Category.assoc, specMap_comp]) _ _ _ _
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  · rw [← Category.assoc, hact', Category.assoc, hact, Category.assoc]
  · obtain ⟨P₁, hP₁⟩ := hlev' t' P hP
    obtain ⟨P₀, hP₀⟩ := hlev (t' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩ ⟨P₁, hP₁⟩
    exact ⟨P₀, by rw [hP₀, Category.assoc]⟩
  · rw [← Category.assoc, hgen', Category.assoc, hgen, ← Category.assoc, ← specMap_comp]

end WithFullLevel.IsPullback
p2m_export "CerednikDrinfeld.QM.ZUniq" "WithFullLevel.IsPullback.trans"
end CerednikDrinfeld.QM.ZUniq

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace ZUniq
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

variable (N m : ℕ)

abbrev PtMap {S : Type} [CommRing S] (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)
    {Z : Scheme.{0}} (ζ : Z ⟶ Spec (CommRingCat.of S)) : Type 1 :=
  ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ

def Represents {S : Type} [CommRing S] (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)
    {Z : Scheme.{0}} (ζ : Z ⟶ Spec (CommRingCat.of S)) (ptZ : PtMap N m u ζ) : Prop :=
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

variable {N m}

section Rep

variable {S : Type} [CommRing S] {u : FakeEllipticCurve.WithFullLevel Λ 1 m S}
  {Z : Scheme.{0}} {ζ : Z ⟶ Spec (CommRingCat.of S)} {ptZ : PtMap N m u ζ}

theorem pt_congr (ptZ : PtMap N m u ζ) {T : Type} [CommRing T] {ρ₁ ρ₂ : S →+* T} (e : ρ₁ = ρ₂)
    (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
    (h₁ : FakeEllipticCurve.WithFullLevel.IsPullback ρ₁ u u')
    (h₂ : FakeEllipticCurve.WithFullLevel.IsPullback ρ₂ u u') (K : u'.1.ExtraLevel N) :
    (ptZ T ρ₁ u' h₁ K).1 = (ptZ T ρ₂ u' h₂ K).1 := by
  subst e; rfl

theorem Represents.coe_eq_of_comparison (hR : Represents N m u ζ ptZ)
    {T : Type} [CommRing T] (ρ : S →+* T) (u' u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
    (h' : FakeEllipticCurve.WithFullLevel.IsPullback ρ u u')
    (h'' : FakeEllipticCurve.WithFullLevel.IsPullback ρ u u'')
    (k : u''.1.A ⟶ u'.1.A) (hk : FakeEllipticCurve.IsPullbackVia (RingHom.id T) u'.1 u''.1 k)
    (hgen : (u''.2.P).1 ≫ k = Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ (u'.2.P).1)
    (K₃ : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N)
    (htr : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u''.1.f),
      FactorsThrough K''.levK P → ∃ P₀ : X ⟶ K₃.K, P₀ ≫ K₃.levK = P.1 ≫ k) :
    (ptZ T ρ u'' h'' K'').1 = (ptZ T ρ u' h' K₃).1 := by
  have h₂ : FakeEllipticCurve.WithFullLevel.IsPullback ((RingHom.id T).comp ρ) u u'' := by
    rw [RingHom.id_comp]; exact h''
  have := hR.2.1 T T ρ (RingHom.id T) u' u'' h' h₂ K₃ K'' k hk hgen htr
  rw [specMap_id, Category.id_comp] at this
  rw [← this]
  exact pt_congr ptZ (RingHom.id_comp ρ).symm u'' h'' h₂ K''

end Rep

end CerednikDrinfeld.QM.ZUniq

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace ZUniq
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}

section TwoRep

variable {S S₀ : Type} [CommRing S] [CommRing S₀]
  {u : FakeEllipticCurve.WithFullLevel Λ 1 m S} {u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m S₀}
  {Z Z₀ : Scheme.{0}} {ζ : Z ⟶ Spec (CommRingCat.of S)} {ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀)}
  {ptZ : PtMap N m u ζ} {ptZ₀ : PtMap N m u₀ ζ₀} {φ₀ : S →+* S₀}

theorem coe_eq_iff_coe_eq (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    {T : Type} [CommRing T] (ρ : S₀ →+* T)
    (u' u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
    (h' : FakeEllipticCurve.WithFullLevel.IsPullback ρ u₀ u')
    (h'' : FakeEllipticCurve.WithFullLevel.IsPullback ρ u₀ u'')
    (hA' : FakeEllipticCurve.WithFullLevel.IsPullback (ρ.comp φ₀) u u')
    (hA'' : FakeEllipticCurve.WithFullLevel.IsPullback (ρ.comp φ₀) u u'')
    (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) :
    (ptZ₀ T ρ u' h' K').1 = (ptZ₀ T ρ u'' h'' K'').1 ↔
      (ptZ T (ρ.comp φ₀) u' hA' K').1 = (ptZ T (ρ.comp φ₀) u'' hA'' K'').1 := by
  have h'c := h'
  have h''c := h''
  obtain ⟨g', hg', hmul', hact', hlev', hgen'⟩ := h'c
  obtain ⟨g'', hg'', hmul'', hact'', hlev'', hgen''⟩ := h''c
  have via' : FakeEllipticCurve.IsPullbackVia ρ u₀.1 u'.1 g' := ⟨hg', hmul', hact', hlev'⟩
  have via'' : FakeEllipticCurve.IsPullbackVia ρ u₀.1 u''.1 g'' := ⟨hg'', hmul'', hact'', hlev''⟩
  obtain ⟨k, hkf, hkg, -, hkvia, -, -, K₃, hK₃⟩ :=
    FakeEllipticCurve.exists_comparison_of_isPullbackVia ρ u₀.1 u'.1 u''.1 g' g'' via' via'' K''
  have hgen : (u''.2.P).1 ≫ k = Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ (u'.2.P).1 := by
    apply hg'.hom_ext
    · rw [Category.assoc, hkg, hgen'', Category.assoc, hgen', specMap_id, Category.id_comp]
    · rw [Category.assoc, hkf, (u''.2.P).2, Category.assoc, (u'.2.P).2, specMap_id, Category.id_comp]
  have htr : ∀ {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u''.1.f),
      FactorsThrough K''.levK P → ∃ P₀ : X ⟶ K₃.K, P₀ ≫ K₃.levK = P.1 ≫ k :=
    fun t P hP => (hK₃ t P).mpr hP
  have eA := hZ.coe_eq_of_comparison (ρ.comp φ₀) u' u'' hA' hA'' k hkvia hgen K₃ K'' htr
  have eB := hZ₀.coe_eq_of_comparison ρ u' u'' h' h'' k hkvia hgen K₃ K'' htr
  constructor
  · intro h
    have e1 : ptZ₀ T ρ u' h' K' = ptZ₀ T ρ u' h' K₃ := Subtype.ext (h.trans eB)
    have e2 := hZ.1 T (ρ.comp φ₀) u' hA' K' K₃ (hZ₀.2.2.2 T ρ u' h' K' K₃ e1)
    rw [show (ptZ T (ρ.comp φ₀) u' hA' K').1 = (ptZ T (ρ.comp φ₀) u' hA' K₃).1 from
      congrArg Subtype.val e2, eA]
  · intro h
    have e1 : ptZ T (ρ.comp φ₀) u' hA' K' = ptZ T (ρ.comp φ₀) u' hA' K₃ := Subtype.ext (h.trans eA)
    have e2 := hZ₀.1 T ρ u' h' K' K₃ (hZ.2.2.2 T (ρ.comp φ₀) u' hA' K' K₃ e1)
    rw [show (ptZ₀ T ρ u' h' K').1 = (ptZ₀ T ρ u' h' K₃).1 from congrArg Subtype.val e2, eB]

end TwoRep

end CerednikDrinfeld.QM.ZUniq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld.QM NeronModelInfra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace ZUniq
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}

noncomputable section

section Main

variable {S S₀ : Type} [CommRing S] [CommRing S₀]
  {u : FakeEllipticCurve.WithFullLevel Λ 1 m S} {u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m S₀}
  {Z Z₀ : Scheme.{0}} {ζ : Z ⟶ Spec (CommRingCat.of S)} {ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀)}
  {ptZ : PtMap N m u ζ} {ptZ₀ : PtMap N m u₀ ζ₀} {φ₀ : S →+* S₀}

def psi (ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀)) {C : Type} [CommRing C] (z : Spec (CommRingCat.of C) ⟶ Z₀) :
    S₀ →+* C :=
  (exists_eq_specMap (z ≫ ζ₀)).choose

theorem spec_psi (ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀)) {C : Type} [CommRing C] (z : Spec (CommRingCat.of C) ⟶ Z₀) :
    Spec.map (CommRingCat.ofHom (psi ζ₀ z)) = z ≫ ζ₀ :=
  (exists_eq_specMap (z ≫ ζ₀)).choose_spec

variable (u₀) in

def model {C : Type} [CommRing C] (ψ : S₀ →+* C) : FakeEllipticCurve.WithFullLevel Λ 1 m C :=
  (FakeEllipticCurve.WithFullLevel.exists_isPullback ψ u₀).choose

variable (u₀) in
theorem model_spec {C : Type} [CommRing C] (ψ : S₀ →+* C) :
    FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ (model u₀ ψ) :=
  (FakeEllipticCurve.WithFullLevel.exists_isPullback ψ u₀).choose_spec

def level (hZ₀ : Represents N m u₀ ζ₀ ptZ₀) {C : Type} [CommRing C] (ψ : S₀ →+* C)
    (z : Spec (CommRingCat.of C) ⟶ Z₀) (hz : z ≫ ζ₀ = Spec.map (CommRingCat.ofHom ψ)) :
    (model u₀ ψ).1.ExtraLevel N :=
  (hZ₀.2.2.1 C ψ (model u₀ ψ) (model_spec u₀ ψ) ⟨z, hz⟩).choose

theorem level_spec (hZ₀ : Represents N m u₀ ζ₀ ptZ₀) {C : Type} [CommRing C] (ψ : S₀ →+* C)
    (z : Spec (CommRingCat.of C) ⟶ Z₀) (hz : z ≫ ζ₀ = Spec.map (CommRingCat.ofHom ψ)) :
    ptZ₀ C ψ (model u₀ ψ) (model_spec u₀ ψ) (level hZ₀ ψ z hz) = ⟨z, hz⟩ :=
  (hZ₀.2.2.1 C ψ (model u₀ ψ) (model_spec u₀ ψ) ⟨z, hz⟩).choose_spec

def eta (hZ₀ : Represents N m u₀ ζ₀ ptZ₀) (ptZ : PtMap N m u ζ)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    (C : Type) [CommRing C] [Algebra S C] (z : Spec (CommRingCat.of C) ⟶ Z₀)
    (_hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C))) :
    Spec (CommRingCat.of C) ⟶ Z :=
  (ptZ C ((psi ζ₀ z).comp φ₀) (model u₀ (psi ζ₀ z)) (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ _))
    (level hZ₀ (psi ζ₀ z) z (spec_psi ζ₀ z).symm)).1

theorem eta_over (hZ₀ : Represents N m u₀ ζ₀ ptZ₀) (ptZ : PtMap N m u ζ)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    (C : Type) [CommRing C] [Algebra S C] (z : Spec (CommRingCat.of C) ⟶ Z₀)
    (hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C))) :
    eta hZ₀ ptZ hu₀ C z hz ≫ ζ = Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
  unfold eta
  rw [(ptZ C _ _ _ _).2, specMap_comp, spec_psi, Category.assoc, hz]

theorem eta_eq (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C : Type} [CommRing C] [Algebra S C] (z : Spec (CommRingCat.of C) ⟶ Z₀)
    (hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C)))
    (ψ : S₀ →+* C) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m C)
    (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ u')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u u') (K : u'.1.ExtraLevel N)
    (hK : (ptZ₀ C ψ u' hu' K).1 = z) :
    eta hZ₀ ptZ hu₀ C z hz = (ptZ C (ψ.comp φ₀) u' hu K).1 := by
  have e : psi ζ₀ z = ψ :=
    ringHom_eq_of_specMap_eq _ _ (by rw [spec_psi, ← hK, (ptZ₀ C ψ u' hu' K).2])
  subst e
  unfold eta
  exact (coe_eq_iff_coe_eq hZ hZ₀ (psi ζ₀ z) (model u₀ (psi ζ₀ z)) u' (model_spec u₀ _) hu'
    (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ _)) hu (level hZ₀ (psi ζ₀ z) z (spec_psi ζ₀ z).symm) K).mp
    (by rw [level_spec hZ₀, hK])

theorem eta_natural (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    (C C' : Type) [CommRing C] [CommRing C'] [Algebra S C] [Algebra S C'] (g : C →ₐ[S] C')
    (z : Spec (CommRingCat.of C) ⟶ Z₀)
    (hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C)))
    (hz' : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ z) ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap S C'))) :
    eta hZ₀ ptZ hu₀ C' (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ z) hz' =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ eta hZ₀ ptZ hu₀ C z hz := by
  set ψ := psi ζ₀ z
  set χ := g.toRingHom

  obtain ⟨u'', K'', gm, hW, hvia, hgen, hKiff⟩ :=
    FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_extraLevel χ (model u₀ ψ)
      (level hZ₀ ψ z (spec_psi ζ₀ z).symm)
  have htr : ∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of C')) (P : SchemeHomOver t u''.1.f),
      FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ (level hZ₀ ψ z (spec_psi ζ₀ z).symm).K,
        P₀ ≫ (level hZ₀ ψ z (spec_psi ζ₀ z).symm).levK = P.1 ≫ gm := fun t P hP => (hKiff t P).mp hP
  have hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u (model u₀ ψ) :=
    WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)

  have eZ := hZ.2.1 C C' (ψ.comp φ₀) χ (model u₀ ψ) u'' hu
    (WithFullLevel.IsPullback.trans (φ := ψ.comp φ₀) (ψ := χ) hu hW) _ K'' gm hvia hgen htr
  have eZ₀ := hZ₀.2.1 C C' ψ χ (model u₀ ψ) u'' (model_spec u₀ ψ)
    (WithFullLevel.IsPullback.trans (model_spec u₀ ψ) hW) _ K'' gm hvia hgen htr
  rw [level_spec hZ₀] at eZ₀

  have hu2 : FakeEllipticCurve.WithFullLevel.IsPullback ((χ.comp ψ).comp φ₀) u u'' := by
    have h := WithFullLevel.IsPullback.trans (φ := ψ.comp φ₀) (ψ := χ) hu hW
    exact h
  rw [eta_eq hZ hZ₀ hu₀ _ hz' (χ.comp ψ) u'' (WithFullLevel.IsPullback.trans (model_spec u₀ ψ) hW) hu2 K'' eZ₀]
  exact eZ

theorem exists_e (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀) :
    ∃ e : Z₀ ⟶ Z, e ≫ ζ = ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀) ∧
      (∀ (C : Type) [CommRing C] [Algebra S C] (z : Spec (CommRingCat.of C) ⟶ Z₀)
        (hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C))),
        z ≫ e = eta hZ₀ ptZ hu₀ C z hz) ∧
      ∀ v : Z₀ ⟶ Z,
        (∀ (C : Type) [CommRing C] [Algebra S C] (z : Spec (CommRingCat.of C) ⟶ Z₀)
          (hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C))),
          z ≫ v = eta hZ₀ ptZ hu₀ C z hz) → v = e :=
  AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural
    (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) ζ (eta hZ₀ ptZ hu₀) (eta_over hZ₀ ptZ hu₀)
    (fun C C' _ _ _ _ g z hz hz' => eta_natural hZ hZ₀ hu₀ C C' g z hz hz')

theorem compat_of_pts (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀) (e : Z₀ ⟶ Z)
    (he : ∀ (C : Type) [CommRing C] [Algebra S C] (z : Spec (CommRingCat.of C) ⟶ Z₀)
        (hz : z ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S C))),
        z ≫ e = eta hZ₀ ptZ hu₀ C z hz)
    (T : Type) [CommRing T] (ψ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
    (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ u')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u u') (K : u'.1.ExtraLevel N) :
    (ptZ₀ T ψ u' hu' K).1 ≫ e = (ptZ T (ψ.comp φ₀) u' hu K).1 := by
  letI : Algebra S T := (ψ.comp φ₀).toAlgebra
  have hz : (ptZ₀ T ψ u' hu' K).1 ≫ (ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [← Category.assoc, (ptZ₀ T ψ u' hu' K).2, ← specMap_comp]
  rw [he T _ hz]
  exact eta_eq hZ hZ₀ hu₀ _ hz ψ u' hu' hu K rfl

end Main

end

end CerednikDrinfeld.QM.ZUniq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld.QM NeronModelInfra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace ZUniq
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}

noncomputable section

section Inverse

variable {S S₀ : Type} [CommRing S] [CommRing S₀]
  {u : FakeEllipticCurve.WithFullLevel Λ 1 m S} {u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m S₀}
  {Z Z₀ : Scheme.{0}} {ζ : Z ⟶ Spec (CommRingCat.of S)} {ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀)}
  {ptZ : PtMap N m u ζ} {ptZ₀ : PtMap N m u₀ ζ₀} {φ₀ : S →+* S₀}

def levelZ (hZ : Represents N m u ζ ptZ) (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C : Type} [CommRing C] (ψ : S₀ →+* C) (zZ : Spec (CommRingCat.of C) ⟶ Z)
    (hzZ : zZ ≫ ζ = Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) : (model u₀ ψ).1.ExtraLevel N :=
  (hZ.2.2.1 C (ψ.comp φ₀) (model u₀ ψ) (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)) ⟨zZ, hzZ⟩).choose

theorem levelZ_spec (hZ : Represents N m u ζ ptZ) (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C : Type} [CommRing C] (ψ : S₀ →+* C) (zZ : Spec (CommRingCat.of C) ⟶ Z)
    (hzZ : zZ ≫ ζ = Spec.map (CommRingCat.ofHom (ψ.comp φ₀))) :
    ptZ C (ψ.comp φ₀) (model u₀ ψ) (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)) (levelZ hZ hu₀ ψ zZ hzZ) =
      ⟨zZ, hzZ⟩ :=
  (hZ.2.2.1 C (ψ.comp φ₀) (model u₀ ψ) (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)) ⟨zZ, hzZ⟩).choose_spec

theorem fst_over {C : Type} [CommRing C] (ψ : S₀ →+* C)
    (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
    (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom ψ)) :
    (w ≫ pullback.fst ζ (Spec.map (CommRingCat.ofHom φ₀))) ≫ ζ = Spec.map (CommRingCat.ofHom (ψ.comp φ₀)) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw, specMap_comp]

def theta (hZ : Represents N m u ζ ptZ) (ptZ₀ : PtMap N m u₀ ζ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C : Type} [CommRing C] (ψ : S₀ →+* C)
    (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
    (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom ψ)) :
    Spec (CommRingCat.of C) ⟶ Z₀ :=
  (ptZ₀ C ψ (model u₀ ψ) (model_spec u₀ ψ)
    (levelZ hZ hu₀ ψ (w ≫ pullback.fst ζ (Spec.map (CommRingCat.ofHom φ₀))) (fst_over ψ w hw))).1

theorem theta_over (hZ : Represents N m u ζ ptZ) (ptZ₀ : PtMap N m u₀ ζ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C : Type} [CommRing C] (ψ : S₀ →+* C)
    (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
    (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom ψ)) :
    theta hZ ptZ₀ hu₀ ψ w hw ≫ ζ₀ = Spec.map (CommRingCat.ofHom ψ) :=
  (ptZ₀ C ψ _ _ _).2

theorem theta_eq (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C : Type} [CommRing C] (ψ : S₀ →+* C)
    (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
    (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom ψ))
    (u' : FakeEllipticCurve.WithFullLevel Λ 1 m C)
    (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ u')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u u') (K : u'.1.ExtraLevel N)
    (hK : (ptZ C (ψ.comp φ₀) u' hu K).1 = w ≫ pullback.fst ζ (Spec.map (CommRingCat.ofHom φ₀))) :
    theta hZ ptZ₀ hu₀ ψ w hw = (ptZ₀ C ψ u' hu' K).1 := by
  unfold theta
  refine (coe_eq_iff_coe_eq hZ hZ₀ ψ (model u₀ ψ) u' (model_spec u₀ ψ) hu'
    (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)) hu _ K).mpr ?_
  rw [levelZ_spec hZ hu₀, hK]

theorem theta_natural (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C C' : Type} [CommRing C] [CommRing C'] (ψ : S₀ →+* C) (χ : C →+* C')
    (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
    (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom ψ))
    (hw' : (Spec.map (CommRingCat.ofHom χ) ≫ w) ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) =
      Spec.map (CommRingCat.ofHom (χ.comp ψ))) :
    theta hZ ptZ₀ hu₀ (χ.comp ψ) (Spec.map (CommRingCat.ofHom χ) ≫ w) hw' =
      Spec.map (CommRingCat.ofHom χ) ≫ theta hZ ptZ₀ hu₀ ψ w hw := by

  set K := levelZ hZ hu₀ ψ (w ≫ pullback.fst ζ (Spec.map (CommRingCat.ofHom φ₀))) (fst_over ψ w hw) with hKdef
  obtain ⟨u'', K'', gm, hW, hvia, hgen, hKiff⟩ :=
    FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_extraLevel χ (model u₀ ψ) K
  have htr : ∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of C')) (P : SchemeHomOver t u''.1.f),
      FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ gm := fun t P hP => (hKiff t P).mp hP
  have hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u (model u₀ ψ) :=
    WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)
  have hu''₀ : FakeEllipticCurve.WithFullLevel.IsPullback (χ.comp ψ) u₀ u'' :=
    WithFullLevel.IsPullback.trans (model_spec u₀ ψ) hW
  have hu''u : FakeEllipticCurve.WithFullLevel.IsPullback (χ.comp (ψ.comp φ₀)) u u'' :=
    WithFullLevel.IsPullback.trans hu hW

  have eZ₀ := hZ₀.2.1 C C' ψ χ (model u₀ ψ) u'' (model_spec u₀ ψ) hu''₀ K K'' gm hvia hgen htr
  have eZ := hZ.2.1 C C' (ψ.comp φ₀) χ (model u₀ ψ) u'' hu hu''u K K'' gm hvia hgen htr
  rw [levelZ_spec hZ hu₀] at eZ

  have hidx : χ.comp (ψ.comp φ₀) = (χ.comp ψ).comp φ₀ := (RingHom.comp_assoc _ _ _).symm
  have hu''u' : FakeEllipticCurve.WithFullLevel.IsPullback ((χ.comp ψ).comp φ₀) u u'' := hidx ▸ hu''u
  have e1 := theta_eq hZ hZ₀ hu₀ (χ.comp ψ) (Spec.map (CommRingCat.ofHom χ) ≫ w) hw' u'' hu''₀ hu''u' K''
    (by rw [← pt_congr ptZ hidx u'' hu''u hu''u' K'', eZ, Category.assoc])
  rw [e1, eZ₀]
  rfl

theorem theta_natural' (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {C C' : Type} [CommRing C] [CommRing C'] (ψ : S₀ →+* C) (χ : C →+* C') (ψ' : S₀ →+* C') (hψ' : χ.comp ψ = ψ')
    (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
    (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom ψ))
    (hw' : (Spec.map (CommRingCat.ofHom χ) ≫ w) ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) =
      Spec.map (CommRingCat.ofHom ψ')) :
    theta hZ ptZ₀ hu₀ ψ' (Spec.map (CommRingCat.ofHom χ) ≫ w) hw' =
      Spec.map (CommRingCat.ofHom χ) ≫ theta hZ ptZ₀ hu₀ ψ w hw := by
  subst hψ'
  exact theta_natural hZ hZ₀ hu₀ ψ χ w hw hw'

theorem exists_inverse (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    (e : Z₀ ⟶ Z) (he : e ≫ ζ = ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀))
    (hcompat : ∀ (T : Type) [CommRing T] (ψ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
        (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ u')
        (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u u') (K : u'.1.ExtraLevel N),
        (ptZ₀ T ψ u' hu' K).1 ≫ e = (ptZ T (ψ.comp φ₀) u' hu K).1) :
    ∃ d : pullback ζ (Spec.map (CommRingCat.ofHom φ₀)) ⟶ Z₀,
      d ≫ ζ₀ = pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) ∧
      ∀ (C : Type) [CommRing C] [Algebra S₀ C]
        (w : Spec (CommRingCat.of C) ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)))
        (hw : w ≫ pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)) = Spec.map (CommRingCat.ofHom (algebraMap S₀ C)))
        (u' : FakeEllipticCurve.WithFullLevel Λ 1 m C)
        (hu' : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap S₀ C) u₀ u')
        (hu : FakeEllipticCurve.WithFullLevel.IsPullback ((algebraMap S₀ C).comp φ₀) u u') (K : u'.1.ExtraLevel N),
        (ptZ C ((algebraMap S₀ C).comp φ₀) u' hu K).1 = w ≫ pullback.fst ζ (Spec.map (CommRingCat.ofHom φ₀)) →
          w ≫ d = (ptZ₀ C (algebraMap S₀ C) u' hu' K).1 := by
  obtain ⟨d, hd, hdpt, -⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural (R := S₀)
      (pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀))) ζ₀
      (fun C _ _ w hw => theta hZ ptZ₀ hu₀ (algebraMap S₀ C) w hw)
      (fun C _ _ w hw => theta_over hZ ptZ₀ hu₀ (algebraMap S₀ C) w hw)
      (fun C C' _ _ _ _ g w hw hw' =>
        theta_natural' hZ hZ₀ hu₀ (algebraMap S₀ C) g.toRingHom (algebraMap S₀ C') g.comp_algebraMap w hw hw')
  refine ⟨d, hd, fun C _ _ w hw u' hu' hu K hK => ?_⟩
  rw [hdpt C w hw]
  exact theta_eq hZ hZ₀ hu₀ (algebraMap S₀ C) w hw u' hu' hu K hK

end Inverse

end

end CerednikDrinfeld.QM.ZUniq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld.QM NeronModelInfra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithFullLevel FakeEllipticCurve.WithFullLevel.IsPullback FakeEllipticCurve.WithExtraLevel mapPt FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.WithFullLevel.exists_isPullback"
namespace ZUniq
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}

theorem isPullback_of_compat {S S₀ : Type} [CommRing S] [CommRing S₀]
    {u : FakeEllipticCurve.WithFullLevel Λ 1 m S} {u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m S₀}
    {Z Z₀ : Scheme.{0}} {ζ : Z ⟶ Spec (CommRingCat.of S)} {ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀)}
    {ptZ : PtMap N m u ζ} {ptZ₀ : PtMap N m u₀ ζ₀} {φ₀ : S →+* S₀}
    (hZ : Represents N m u ζ ptZ) (hZ₀ : Represents N m u₀ ζ₀ ptZ₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    (e : Z₀ ⟶ Z) (he : e ≫ ζ = ζ₀ ≫ Spec.map (CommRingCat.ofHom φ₀))
    (hcompat : ∀ (T : Type) [CommRing T] (ψ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
        (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ u')
        (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u u') (K : u'.1.ExtraLevel N),
        (ptZ₀ T ψ u' hu' K).1 ≫ e = (ptZ T (ψ.comp φ₀) u' hu K).1) :
    CategoryTheory.IsPullback e ζ₀ ζ (Spec.map (CommRingCat.ofHom φ₀)) := by
  obtain ⟨d, hd, hdpts⟩ := exists_inverse hZ hZ₀ hu₀ e he hcompat
  let c : Z₀ ⟶ pullback ζ (Spec.map (CommRingCat.ofHom φ₀)) := pullback.lift e ζ₀ he
  have hc_fst : c ≫ pullback.fst _ _ = e := pullback.lift_fst _ _ _
  have hc_snd : c ≫ pullback.snd _ _ = ζ₀ := pullback.lift_snd _ _ _

  have hcd : c ≫ d = 𝟙 Z₀ := by
    obtain ⟨v, -, -, hvu⟩ :=
      AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural (R := S₀) ζ₀ ζ₀
        (fun C _ _ z _ => z) (fun C _ _ z hz => hz) (fun C C' _ _ _ _ g z hz hz' => rfl)
    rw [hvu (𝟙 Z₀) (fun C _ _ z hz => Category.comp_id _)]
    apply hvu
    intro C _ _ z hz
    set ψ := algebraMap S₀ C
    obtain ⟨Kz, hKz⟩ := hZ₀.2.2.1 C ψ (model u₀ ψ) (model_spec u₀ ψ) ⟨z, hz⟩
    have hu := WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)
    have hz' : (ptZ₀ C ψ (model u₀ ψ) (model_spec u₀ ψ) Kz).1 = z := congrArg Subtype.val hKz
    have hw : (z ≫ c) ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap S₀ C)) := by
      rw [Category.assoc, hc_snd]; exact hz
    have hfst : (ptZ C (ψ.comp φ₀) (model u₀ ψ) hu Kz).1 = (z ≫ c) ≫ pullback.fst _ _ := by
      rw [Category.assoc, hc_fst, ← hcompat C ψ (model u₀ ψ) (model_spec u₀ ψ) hu Kz, hz']
    rw [← Category.assoc, hdpts C (z ≫ c) hw (model u₀ ψ) (model_spec u₀ ψ) hu Kz hfst, hz']

  have hdc : d ≫ c = 𝟙 _ := by
    obtain ⟨v, -, -, hvu⟩ :=
      AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural (R := S₀)
        (pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀))) (pullback.snd ζ (Spec.map (CommRingCat.ofHom φ₀)))
        (fun C _ _ w _ => w) (fun C _ _ w hw => hw) (fun C C' _ _ _ _ g w hw hw' => rfl)
    rw [hvu (𝟙 _) (fun C _ _ w hw => Category.comp_id _)]
    apply hvu
    intro C _ _ w hw
    set ψ := algebraMap S₀ C
    have hu := WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ ψ)
    have hwf : (w ≫ pullback.fst _ _) ≫ ζ = Spec.map (CommRingCat.ofHom (ψ.comp φ₀)) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, ← specMap_comp]
    obtain ⟨K, hK⟩ := hZ.2.2.1 C (ψ.comp φ₀) (model u₀ ψ) hu ⟨w ≫ pullback.fst _ _, hwf⟩
    have hK' : (ptZ C (ψ.comp φ₀) (model u₀ ψ) hu K).1 = w ≫ pullback.fst _ _ := congrArg Subtype.val hK
    rw [← Category.assoc, hdpts C w hw (model u₀ ψ) (model_spec u₀ ψ) hu K hK']
    apply pullback.hom_ext
    · rw [Category.assoc, hc_fst, hcompat C ψ (model u₀ ψ) (model_spec u₀ ψ) hu K, hK']
    · rw [Category.assoc, hc_snd, (ptZ₀ C ψ _ _ K).2, hw]
  haveI : IsIso c := ⟨⟨d, hcd, hdc⟩⟩
  exact IsPullback.of_iso_pullback ⟨he⟩ (asIso c) hc_fst hc_snd

end CerednikDrinfeld.QM.ZUniq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel.CerednikDrinfeld.QM NeronModelInfra"

open CerednikDrinfeld.QM.ZUniq in

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    {S : Type} [CommRing S] (u : FakeEllipticCurve.WithFullLevel Λ 1 m S)
    {Z : Scheme.{0}} (ζ : Z ⟶ Spec (CommRingCat.of S))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ)
    (hZ : (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
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
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P))
    {S₀ : Type} [CommRing S₀] (φ₀ : S →+* S₀) (u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m S₀)
    (hu₀ : FakeEllipticCurve.WithFullLevel.IsPullback φ₀ u u₀)
    {Z₀ : Scheme.{0}} (ζ₀ : Z₀ ⟶ Spec (CommRingCat.of S₀))
    (ptZ₀ : ∀ (T : Type) [CommRing T] (φ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T),
          FakeEllipticCurve.WithFullLevel.IsPullback φ u₀ u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₀)
    (hZ₀ : (∀ (T : Type) [CommRing T] (φ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u₀ u') (K K' : u'.1.ExtraLevel N),
            (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) → ptZ₀ T φ u' hu' K = ptZ₀ T φ u' hu' K') ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S₀ →+* T) (ψ : T →+* T')
            (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T) (u'' : FakeEllipticCurve.WithFullLevel Λ 1 m T')
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u₀ u')
            (hu'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u₀ u'')
            (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) (g : u''.1.A ⟶ u'.1.A),

            FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g →
            (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
            (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
              FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) →
              (ptZ₀ T' (ψ.comp φ) u'' hu'' K'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ₀ T φ u' hu' K').1) ∧

        (∀ (T : Type) [CommRing T] (φ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u₀ u')
            (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₀), ∃ K : u'.1.ExtraLevel N, ptZ₀ T φ u' hu' K = z) ∧
        (∀ (T : Type) [CommRing T] (φ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u₀ u')
            (K K' : u'.1.ExtraLevel N), ptZ₀ T φ u' hu' K = ptZ₀ T φ u' hu' K' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P)) :
    ∃! e : Z₀ ⟶ Z,
      CategoryTheory.IsPullback e ζ₀ ζ (Spec.map (CommRingCat.ofHom φ₀)) ∧
      ∀ (T : Type) [CommRing T] (ψ : S₀ →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m T)
        (hu' : FakeEllipticCurve.WithFullLevel.IsPullback ψ u₀ u')
        (hu : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ₀) u u') (K : u'.1.ExtraLevel N),
        (ptZ₀ T ψ u' hu' K).1 ≫ e = (ptZ T (ψ.comp φ₀) u' hu K).1 := by
  have hZ' : CerednikDrinfeld.QM.ZUniq.Represents N m u ζ ptZ := hZ
  have hZ₀' : CerednikDrinfeld.QM.ZUniq.Represents N m u₀ ζ₀ ptZ₀ := hZ₀
  obtain ⟨e, he, hpts, huniq⟩ := exists_e hZ' hZ₀' hu₀
  have hcompat := compat_of_pts hZ' hZ₀' hu₀ e hpts
  refine ⟨e, ⟨isPullback_of_compat hZ' hZ₀' hu₀ e he hcompat, hcompat⟩, ?_⟩
  rintro e' ⟨-, hcompat'⟩
  apply huniq e'
  intro C _ _ z hz
  have hzψ : z ≫ ζ₀ = Spec.map (CommRingCat.ofHom (psi ζ₀ z)) := (spec_psi ζ₀ z).symm
  have := hcompat' C (psi ζ₀ z) (model u₀ (psi ζ₀ z)) (model_spec u₀ _)
    (WithFullLevel.IsPullback.trans hu₀ (model_spec u₀ _)) (level hZ₀' (psi ζ₀ z) z hzψ)
  rw [level_spec hZ₀'] at this
  exact this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_existsUnique_hom_isPullback_of_represents_extraLevel (solution)
