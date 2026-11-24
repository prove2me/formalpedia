-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:48.954113+00:00
-- url     : https://prove2.me/submissions/f327046b-cbc8-4570-bc69-d06990fb84fa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem support_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl
private theorem isRadical_map_of_bijective {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {I : Ideal R} (hI : I.radical = I) :
    (Ideal.map φ I).radical = Ideal.map φ I := by
  refine le_antisymm ?_ Ideal.le_radical
  intro y hy
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hy
  obtain ⟨z, rfl⟩ := hφ.2 y
  rw [← map_pow] at hm
  obtain ⟨w, hw, hw2⟩ := (Ideal.mem_map_iff_of_surjective φ hφ.2).mp hm
  have hz : z ^ m ∈ I := by
    have hwz : w = z ^ m := hφ.1 hw2
    rwa [hwz] at hw
  have hzI : z ∈ I := by
    rw [← hI]
    exact Ideal.mem_radical_iff.mpr ⟨m, hz⟩
  exact Ideal.mem_map_of_mem _ hzI
private theorem isIso_appLE_image {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h] (U : X.Opens)
    (e : U ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U)) :
    IsIso (h.appLE (h ''ᵁ U) U e) := by
  rw [show h.appLE (h ''ᵁ U) U e = (h.appIso U).hom from (Scheme.Hom.appIso_hom' h U).symm]
  infer_instance
private theorem comap_ideal_radical_eq_of_isOpenImmersion {X' Y' : Scheme.{u}} (h : X' ⟶ Y') [IsOpenImmersion h]
    (I : Y'.IdealSheafData) (hI : I.radical = I) (V : X'.affineOpens) :
    ((I.comap h).ideal V).radical = (I.comap h).ideal V := by
  have hU : IsAffineOpen (h ''ᵁ V.1) := V.2.image_of_isOpenImmersion h
  have he : V.1 ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ V.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq h V.1).symm
  have : IsIso (h.appLE (h ''ᵁ V.1) V.1 he) := isIso_appLE_image h V.1 he
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨h ''ᵁ V.1, hU⟩ V he]
  refine isRadical_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (h.appLE (h ''ᵁ V.1) V.1 he)) ?_
  rw [← Scheme.IdealSheafData.radical_ideal, hI]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X' Y' : Scheme.{u}} (h : X' ⟶ Y')
    [IsOpenImmersion h] (Z : TopologicalSpace.Closeds Y') :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal (closedPreimage h Z) := by
  have hZrad : (Scheme.IdealSheafData.vanishingIdeal Z).radical
      = Scheme.IdealSheafData.vanishingIdeal Z := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, support_vanishingIdeal]
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap h := by
    refine Scheme.IdealSheafData.ext (funext fun V => ?_)
    rw [Scheme.IdealSheafData.radical_ideal]
    exact comap_ideal_radical_eq_of_isOpenImmersion h _ hZrad V
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).support
      = closedPreimage h Z := by
    refine SetLike.ext fun x => ?_
    simp only [Scheme.IdealSheafData.mem_support_comap]
    exact Iff.rfl
  calc (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          ((Scheme.IdealSheafData.vanishingIdeal Z).comap h).support := by
        rw [Scheme.IdealSheafData.vanishingIdeal_support]
    _ = Scheme.IdealSheafData.vanishingIdeal (closedPreimage h Z) := by rw [hsupp]
end FunctorialResolution.EmbeddedResolution
