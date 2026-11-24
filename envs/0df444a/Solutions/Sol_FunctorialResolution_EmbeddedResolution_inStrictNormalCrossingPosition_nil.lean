-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:07.897825+00:00
-- url     : https://prove2.me/submissions/5a7e4718-3c85-47e5-b10f-de38c41729f5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsNil
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPositionAt_nil
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map



set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] :
    InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_nil p x⟩
  intro D hD
  simp at hD
end FunctorialResolution.EmbeddedResolution
