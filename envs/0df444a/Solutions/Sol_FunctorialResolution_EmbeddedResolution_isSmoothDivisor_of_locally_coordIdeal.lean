-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:46.987367+00:00
-- url     : https://prove2.me/submissions/bec49d7e-ce6d-4165-ba7b-e96008cd0d6a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isSmoothDivisor_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
private theorem notMem_support_of_mem_of_restrictIdeal_eq_top {Y : Scheme.{u}}
    (I : Y.IdealSheafData) {U : Y.Opens} (h : restrictIdeal I U = ⊤) {x : Y} (hxU : x ∈ U) :
    x ∉ I.support := by
  intro hx
  have h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
  rw [← restrictIdeal_eq_comap_ι, h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (D : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) :
    IsSmoothDivisor p D := by
  rw [isSmoothDivisor_iff]
  refine ⟨isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal D h, smooth_subschemeι_comp_of_locally_eq_coordIdeal D ?_⟩
  intro x hx
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  rcases hc with hc | ⟨j, hj⟩
  · exact absurd hx (notMem_support_of_mem_of_restrictIdeal_eq_top D hc hxU)
  · exact ⟨U, hxU, n, c, {j}, hj⟩
end FunctorialResolution.EmbeddedResolution
