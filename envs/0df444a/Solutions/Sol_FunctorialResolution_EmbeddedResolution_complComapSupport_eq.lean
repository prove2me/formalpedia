-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.complComapSupport_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:40.279499+00:00
-- url     : https://prove2.me/submissions/13cabb51-9b94-4e4c-b797-ef3aa02cf682

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    complComapSupport π Z = (Z.comap π).support.compl := rfl
end FunctorialResolution.EmbeddedResolution
