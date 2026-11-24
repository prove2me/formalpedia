-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:49.529366+00:00
-- url     : https://prove2.me/submissions/09069675-68c8-4cf8-b2ff-c0f04e85c42a

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
private theorem isIso_appLE_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {W : X.Opens} {V : Y.Opens} (hV : f ''ᵁ W = V) (e : W ≤ f ⁻¹ᵁ V) :
    IsIso (f.appLE V W e) := by
  subst hV
  rw [← Scheme.Hom.appIso_hom']
  infer_instance
private theorem exists_affineOpen_mem_le {X : Scheme.{u}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ W := by
  obtain ⟨Vs, hVs, hxV, hVW⟩ :=
    (Scheme.isBasis_affineOpens X).exists_subset_of_mem_open
      (show x ∈ (W : Set X) from hx) W.isOpen
  obtain ⟨V, hVmem, rfl⟩ := hVs
  exact ⟨⟨V, hVmem⟩, hxV, fun y hy => hVW hy⟩
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {X U : Scheme.{u}}
    {I : X.IdealSheafData} (hI : IsLocallyGeneratedByNonZeroDivisor I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsLocallyGeneratedByNonZeroDivisor (I.comap f) := by
  intro x
  obtain ⟨V, g, hxV, hg, hVg⟩ := hI (f.base x)
  have hVa : IsAffineOpen (V : X.Opens) := V.2
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le x (f ⁻¹ᵁ (V : X.Opens)) hxV
  have hWa : IsAffineOpen (W : U.Opens) := W.2
  have hximg : f.base x ∈ (f ''ᵁ (W : U.Opens)) := ⟨x, hxW, rfl⟩
  obtain ⟨r, hr1, hr2⟩ := hVa.exists_basicOpen_le (⟨f.base x, hximg⟩ : (f ''ᵁ (W : U.Opens))) hxV
  have hW'le : f ⁻¹ᵁ (X.basicOpen r) ≤ (W : U.Opens) := by
    rw [← Scheme.Hom.preimage_image_eq f (W : U.Opens)]
    exact fun y hy => hr1 hy
  have hbas : U.basicOpen ((f.appLE (V : X.Opens) (W : U.Opens) hWle).hom r)
      = f ⁻¹ᵁ (X.basicOpen r) := by
    rw [show (f.appLE (V : X.Opens) (W : U.Opens) hWle).hom r
          = (U.presheaf.map (homOfLE hWle).op).hom ((f.app (V : X.Opens)).hom r) from rfl,
      Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact inf_eq_right.mpr hW'le
  have hW'aff : IsAffineOpen (f ⁻¹ᵁ (X.basicOpen r)) := by
    rw [← hbas]
    exact hWa.basicOpen _
  have hBrange : X.basicOpen r ≤ f.opensRange := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hr1 hy
    exact ⟨z, hz⟩
  have himg : f ''ᵁ (f ⁻¹ᵁ (X.basicOpen r)) = X.basicOpen r :=
    (f.image_preimage_eq_opensRange_inf (X.basicOpen r)).trans (inf_eq_right.mpr hBrange)
  have : IsIso (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl) :=
    isIso_appLE_of_image_eq f himg le_rfl
  have e1 : (I.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
      = I.ideal ⟨X.basicOpen r, hVa.basicOpen r⟩ := I.map_ideal_basicOpen V r
  rw [hVg, Ideal.map_span, Set.image_singleton] at e1
  refine ⟨⟨f ⁻¹ᵁ (X.basicOpen r), hW'aff⟩,
    (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom g), hr2, ?_, ?_⟩
  · refine map_mem_nonZeroDivisors_of_iso
      (asIso (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl)) ?_
    have := hVa.isLocalization_basicOpen r
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) Γ(X, X.basicOpen r) hg
  · have hmap := I.comap_ideal_eq_map_appLE f ⟨X.basicOpen r, hVa.basicOpen r⟩
      ⟨f ⁻¹ᵁ (X.basicOpen r), hW'aff⟩ le_rfl
    rw [← e1, Ideal.map_span, Set.image_singleton] at hmap
    exact hmap
end IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.Blowup
