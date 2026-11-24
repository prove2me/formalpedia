-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.notMem_support_of_mem_opens_of_restrictIdeal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:06:04.802159+00:00
-- url     : https://prove2.me/submissions/0c48820c-d1cc-4f31-9bed-1888eae415a5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData)
    (U : X.Opens) (h : restrictIdeal Z U = ⊤) (x : X) (hx : x ∈ U) : x ∉ Z.support := by
  intro hxZ
  obtain ⟨y, hy⟩ : x ∈ Set.range (⇑U.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hx
  have h' : Z.comap U.ι = ⊤ := h
  have h2 := Scheme.IdealSheafData.support_comap Z U.ι
  have h3 : (⇑U.ι) y ∈ Z.support := by
    rw [hy]
    exact hxZ
  have h4 : y ∈ (Z.comap U.ι).support := by
    rw [h2]
    exact h3
  rw [h', Scheme.IdealSheafData.support_top] at h4
  exact h4
end FunctorialResolution.EmbeddedResolution
