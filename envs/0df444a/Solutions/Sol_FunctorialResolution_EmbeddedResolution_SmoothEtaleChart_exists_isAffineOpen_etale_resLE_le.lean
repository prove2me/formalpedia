-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:45.902505+00:00
-- url     : https://prove2.me/submissions/360d9d60-ba40-4890-8d31-639f4bf2c72d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothEtaleChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FunctorialResolution.EmbeddedResolution
namespace SmoothEtaleChart
private theorem exists_etale_mvPolynomial_ulift {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
    (g : MvPolynomial (Fin n) R →+* S) (hg : g.Etale) (f : R →+* S)
    (hf : g.comp MvPolynomial.C = f) :
    ∃ g' : MvPolynomial (ULift.{u} (Fin n)) R →+* S,
      g'.comp MvPolynomial.C = f ∧ g'.Etale := by
  set E : MvPolynomial (ULift.{u} (Fin n)) R ≃+* MvPolynomial (Fin n) R :=
    (MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingEquiv with hE
  refine ⟨g.comp E.toRingHom, ?_, RingHom.Etale.respectsIso.right g E hg⟩
  refine RingHom.ext fun a => ?_
  have h1 : E (MvPolynomial.C a) = MvPolynomial.C a := by
    simp [hE]
  have h2 : g (MvPolynomial.C a) = f a := by rw [← hf]; rfl
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1, h2]
private theorem exists_etale_over_affineSpace_of_isStandardSmooth {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom φ)) :
    ∃ (d : ℕ) (g : Spec S ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec R)),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) = Spec.map φ := by
  obtain ⟨n, gr, hgrC, hgrEt⟩ := hφ.exists_etale_mvPolynomial
  obtain ⟨g', hg'C, hg'Et⟩ := exists_etale_mvPolynomial_ulift gr hgrEt _ hgrC
  have hSpecEt : Etale (Spec.map (CommRingCat.ofHom g')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact hg'Et
  have hcomp : CommRingCat.ofHom (MvPolynomial.C :
      ↑R →+* MvPolynomial (ULift.{u} (Fin n)) ↑R) ≫ CommRingCat.ofHom g' = φ :=
    CommRingCat.hom_ext hg'C
  refine ⟨n, Spec.map (CommRingCat.ofHom g') ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv, inferInstance, ?_⟩
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  exact congrArg Spec.map hcomp
private theorem resLE_eq_isoSpec_conj_SpecMap_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) {W : X.Opens}
    {V : Y.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W) :
    hV.isoSpec.hom ≫ Spec.map (h.appLE W V e) ≫ hW.isoSpec.inv = h.resLE W V e := by
  rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc]
  rw [hW.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec h hW hV e, ← hV.isoSpec_inv_ι]
  simp
private theorem exists_etale_over_affineSpace_resLE_of_isStandardSmooth {X Y : Scheme.{u}} (h : Y ⟶ X)
    {W : X.Opens} {V : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W)
    (hstd : RingHom.IsStandardSmooth (CommRingCat.Hom.hom (h.appLE W V e))) :
    ∃ (d : ℕ) (g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  obtain ⟨d, g₀, hg₀et, hg₀⟩ :=
    exists_etale_over_affineSpace_of_isStandardSmooth (h.appLE W V e) hstd
  have := hg₀et
  have : IsIso (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) :=
    ⟨⟨AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.hom, by
        rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id], by
        rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]⟩⟩
  have : Etale hV.isoSpec.hom := inferInstance
  have : Etale (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) := inferInstance
  refine ⟨d, hV.isoSpec.hom ≫ g₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, AffineSpace.map_over, ← Category.assoc g₀, hg₀]
  exact resLE_eq_isoSpec_conj_SpecMap_appLE h hW hV e
private theorem smooth_resLE {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (W : X.Opens)
    (V : Y.Opens) (e : V ≤ h ⁻¹ᵁ W) : Smooth (h.resLE W V e) := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U U' e'
  rw [Scheme.Hom.resLE_appLE]
  exact HasRingHomProperty.appLE @Smooth h ‹Smooth h›
    ⟨W.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩
    ⟨V.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩ _
private theorem exists_affineOpen_etale_over_affineSpace_resLE_le {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  have e₀ : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) ≤ h ⁻¹ᵁ W₀ := inf_le_right
  have hy' : y ∈ (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) := ⟨hV₀, hW₀⟩
  have : Smooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) := smooth_resLE h W₀ _ e₀
  obtain ⟨W', hW', V', hV', hyV', e', hstd⟩ :=
    Smooth.exists_isStandardSmooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) ⟨y, hy'⟩
  have h1 : h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀ ≫ W₀.ι = (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ≫ h := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hb : ∀ z : ↥(V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens),
      h.base ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι.base z)
        = W₀.ι.base ((h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z) := by
    intro z
    exact (congrArg (fun m : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).toScheme ⟶ X => m.base z) h1).symm
  have hWle : (W₀.ι ''ᵁ W' : X.Opens) ≤ W₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  have hVle : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ V₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2.1
  have e : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ h ⁻¹ᵁ (W₀.ι ''ᵁ W') := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨(h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z, e' hz, (hb z).symm⟩
  have hWaff : IsAffineOpen (W₀.ι ''ᵁ W' : X.Opens) := hW'.image_of_isOpenImmersion W₀.ι
  have hVaff : IsAffineOpen ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) :=
    hV'.image_of_isOpenImmersion _
  have happ : (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).appLE W' V' e'
      = h.appLE (W₀.ι ''ᵁ W') ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V') e :=
    Scheme.Hom.resLE_appLE h e₀ W' V' e'
  rw [happ] at hstd
  obtain ⟨d, g, hg, hgπ⟩ := exists_etale_over_affineSpace_resLE_of_isStandardSmooth h hWaff hVaff e hstd
  exact ⟨W₀.ι ''ᵁ W', (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V', d, e, hWaff, hVaff,
    ⟨⟨y, hy'⟩, hyV', rfl⟩, hWle, hVle, g, hg, hgπ⟩
end SmoothEtaleChart
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SmoothEtaleChart
namespace FunctorialResolution.EmbeddedResolution.SmoothEtaleChart
theorem _root_.solution {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e :=
  exists_affineOpen_etale_over_affineSpace_resLE_le h y W₀ hW₀ V₀ hV₀
end FunctorialResolution.EmbeddedResolution.SmoothEtaleChart
