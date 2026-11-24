-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.mem_support_iff_of_agreeNear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:37.782278+00:00
-- url     : https://prove2.me/submissions/4e7b351f-27a0-4457-bef7-6a2d8103b0ef

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support


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
    {W : Scheme.{u}} {I J : W.IdealSheafData} {x : ↥W} (h : AgreeNear I J x) :
    x ∈ (I.support : Set ↥W) ↔ x ∈ (J.support : Set ↥W) := by
  have h1 := hV.orderAt_congr W I J x h
  constructor
  · intro hx
    have hx' : (1 : ℕ∞) ≤ orderAt I x := (one_le_orderAt_iff_mem_support I x).2 hx
    refine (one_le_orderAt_iff_mem_support J x).1 ?_
    rw [← h1]
    exact hx'
  · intro hx
    have hx' : (1 : ℕ∞) ≤ orderAt J x := (one_le_orderAt_iff_mem_support J x).2 hx
    refine (one_le_orderAt_iff_mem_support I x).1 ?_
    rw [h1]
    exact hx'
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
