-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_of_filterNeTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:38.176804+00:00
-- url     : https://prove2.me/submissions/a27a264b-d4fb-414a-ab20-7b1fdee7175e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isSmoothDivisor_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPositionAt_of_filterNeTop_eq
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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
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
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]
private theorem mem_of_mem_filterNeTop {D : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : D ∈ filterNeTop E) : D ∈ E := by
  simp only [filterNeTop, List.mem_filter] at h
  exact h.1
private theorem mem_filterNeTop {D : X.IdealSheafData} {E : List X.IdealSheafData}
    (hD : D ∈ E) (h : D ≠ ⊤) : D ∈ filterNeTop E := by
  simp only [filterNeTop, List.mem_filter]
  exact ⟨hD, by simpa using h⟩
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p E' := by
  rw [inStrictNormalCrossingPosition_iff] at hE ⊢
  obtain ⟨hsm, hpos⟩ := hE
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_filterNeTop_eq p E E' h x (hpos x)⟩
  intro D hD
  by_cases hDt : D = ⊤
  · rw [hDt]
    exact isSmoothDivisor_top p
  · have h1 : D ∈ filterNeTop E' := mem_filterNeTop hD hDt
    rw [← h] at h1
    exact hsm D (mem_of_mem_filterNeTop h1)
end FunctorialResolution.EmbeddedResolution
