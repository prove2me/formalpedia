-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SmoothLocalChart.isPullback_morphismRestrict_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:51.005919+00:00
-- url     : https://prove2.me/submissions/2beea73b-a2d5-4ca0-9432-42cf4f4e6f1a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothLocalChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SmoothLocalChart
variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}
namespace FunctorialResolution.EmbeddedResolution.SmoothLocalChart
theorem _root_.solution (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb :=
  AlgebraicGeometry.isPullback_morphismRestrict H.emb (H.ambient.basicOpen C.func)
end FunctorialResolution.EmbeddedResolution.SmoothLocalChart
