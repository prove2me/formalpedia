-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:29.988832+00:00
-- url     : https://prove2.me/submissions/b2598d51-23f0-45af-8d1e-d0eb21ac5c93

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_FunctorialResolution_Blowup_map_mem_nonZeroDivisors_of_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
namespace FunctorialResolution.Blowup
private theorem eq_span_inv_of_map_eq_span {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ]
    (J : Ideal R) (s : S) (h : J.map φ.hom = Ideal.span {s}) :
    J = Ideal.span {(CategoryTheory.inv φ).hom s} := by
  have hcomp : (CategoryTheory.inv φ).hom.comp φ.hom = RingHom.id R := by
    ext x
    simp
  calc J = (J.map φ.hom).map (CategoryTheory.inv φ).hom := by
        rw [Ideal.map_map, hcomp, Ideal.map_id]
    _ = (Ideal.span {s}).map (CategoryTheory.inv φ).hom := by rw [h]
    _ = Ideal.span {(CategoryTheory.inv φ).hom s} := by rw [Ideal.map_span, Set.image_singleton]
private theorem isIso_appLE_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {W : X.Opens} {V : Y.Opens} (hV : f ''ᵁ W = V) (e : W ≤ f ⁻¹ᵁ V) :
    IsIso (f.appLE V W e) := by
  subst hV
  rw [← Scheme.Hom.appIso_hom']
  infer_instance
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData)
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsLocallyGeneratedByNonZeroDivisor (I.comap (f i))) :
    IsLocallyGeneratedByNonZeroDivisor I := by
  intro x
  obtain ⟨i, u, hu⟩ := hcover x
  obtain ⟨W, s, hxW, hs, hWs⟩ := h i u
  have hWa : IsAffineOpen (W : (U i).Opens) := W.2
  have hVaff : IsAffineOpen (f i ''ᵁ (W : (U i).Opens)) := hWa.image_of_isOpenImmersion (f i)
  have hpre : (f i) ⁻¹ᵁ (f i ''ᵁ (W : (U i).Opens)) = (W : (U i).Opens) :=
    Scheme.Hom.preimage_image_eq (f i) _
  have e : (W : (U i).Opens) ≤ (f i) ⁻¹ᵁ (f i ''ᵁ (W : (U i).Opens)) := hpre.ge
  have : IsIso ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e) :=
    isIso_appLE_of_image_eq (f i) rfl e
  have key := I.comap_ideal_eq_map_appLE (f i) ⟨f i ''ᵁ (W : (U i).Opens), hVaff⟩ W e
  rw [hWs] at key
  refine ⟨⟨f i ''ᵁ (W : (U i).Opens), hVaff⟩,
    (CategoryTheory.inv ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e)).hom s,
    ?_, ?_, ?_⟩
  · exact ⟨u, hxW, hu⟩
  · exact map_mem_nonZeroDivisors_of_iso
      (asIso (CategoryTheory.inv
        ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e))) hs
  · exact eq_span_inv_of_map_eq_span _ _ _ key.symm
end IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.Blowup
