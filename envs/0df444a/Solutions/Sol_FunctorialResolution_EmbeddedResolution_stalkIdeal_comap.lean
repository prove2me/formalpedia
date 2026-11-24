-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:14.217174+00:00
-- url     : https://prove2.me/submissions/0df93090-c3ca-40c4-9fbc-7ac82769a906

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem germ_comp_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) :
    (Y.presheaf.germ V y hy).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) (e hy)).hom := by
  have key : h.appLE U V e ≫ Y.presheaf.germ V y hy
      = X.presheaf.germ U (h.base y) (e hy) ≫ h.stalkMap y := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    exact (Scheme.Hom.germ_stalkMap ..).symm
  simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom key
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    stalkIdeal (I.comap h) y =
      Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (show h.base y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show y ∈ h ⁻¹ᵁ U from hxU)
  have hcomp : (Y.presheaf.germ V y hyV).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) hxU).hom :=
    germ_comp_appLE h U V e y hyV
  rw [stalkIdeal_eq_map_germ (I.comap h) y ⟨V, hV⟩ hyV,
    stalkIdeal_eq_map_germ I (h.base y) ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e,
    Ideal.map_map, Ideal.map_map]
  exact congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) hcomp
end FunctorialResolution.EmbeddedResolution
