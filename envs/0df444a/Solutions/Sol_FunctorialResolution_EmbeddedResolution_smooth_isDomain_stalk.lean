-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smooth_isDomain_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:31.775058+00:00
-- url     : https://prove2.me/submissions/abd6dca3-7873-4724-8fa4-855a6d87e152

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isDomain_stalk_of_smooth

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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p) (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have := hp
  exact isDomain_stalk_of_smooth p x
end FunctorialResolution.EmbeddedResolution
