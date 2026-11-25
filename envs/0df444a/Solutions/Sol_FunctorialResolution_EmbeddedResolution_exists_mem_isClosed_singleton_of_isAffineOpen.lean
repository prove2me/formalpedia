-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_mem_isClosed_singleton_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:00.573158+00:00
-- url     : https://prove2.me/submissions/9c86a95f-e3c4-4e44-a234-c0658d86eb8c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isClosed_singleton_of_isAffineOpen

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
theorem _root_.solution {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ x : X, ∃ hx : x ∈ U, IsClosed ({(⟨x, hx⟩ : U.toScheme)} : Set U.toScheme) := by
  obtain ⟨x, hx⟩ := exists_isClosed_singleton_of_isAffineOpen U hU hne
  obtain ⟨y, hy⟩ := x
  exact ⟨y, hy, hx⟩
end FunctorialResolution.EmbeddedResolution
