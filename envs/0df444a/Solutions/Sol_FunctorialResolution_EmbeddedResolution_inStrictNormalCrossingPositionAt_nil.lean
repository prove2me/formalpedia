-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:02.831159+00:00
-- url     : https://prove2.me/submissions/4a16c6af-d147-4d9e-b00f-8c3a91dee7c2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsNil
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
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
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    InStrictNormalCrossingPositionAt p ([] : List X.IdealSheafData) x := by
  obtain ⟨U, m, hxU, _, hc⟩ := exists_etaleChart p x
  obtain ⟨c⟩ := hc
  refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi
end FunctorialResolution.EmbeddedResolution
