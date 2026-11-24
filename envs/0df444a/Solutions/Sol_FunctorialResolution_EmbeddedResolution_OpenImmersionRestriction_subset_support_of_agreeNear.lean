-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.subset_support_of_agreeNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:18.041684+00:00
-- url     : https://prove2.me/submissions/9e354a17-18a8-485d-9965-91615566439e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_mem_support_iff_of_agreeNear


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
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (N : W.IdealSheafData) (T : Set ↥W) (hT : IsClosed T)
    (hagree : ∀ x ∈ T, AgreeNear N (V W ⟨T, hT⟩) x) :
    T ⊆ (N.support : Set ↥W) := by
  intro x hx
  rw [mem_support_iff_of_agreeNear hV (hagree x hx), hV.support_vanishing W ⟨T, hT⟩]
  exact hx
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
