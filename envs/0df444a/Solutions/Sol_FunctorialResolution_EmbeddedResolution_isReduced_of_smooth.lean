-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isReduced_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:09.290061+00:00
-- url     : https://prove2.me/submissions/4817fb4f-06a4-456c-86b2-40977b634f53

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
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth p x
    infer_instance
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk X
end FunctorialResolution.EmbeddedResolution
