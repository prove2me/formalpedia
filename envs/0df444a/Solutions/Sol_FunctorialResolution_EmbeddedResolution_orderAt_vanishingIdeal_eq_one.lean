-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:20:32.051277+00:00
-- url     : https://prove2.me/submissions/72a88e63-8cc6-46e6-b2e4-8be82ca707b2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [IsLocallyNoetherian X] (Z : TopologicalSpace.Closeds X)
    (ξ : X) (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≠ ⊥) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 :=
  orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal _ ξ
    (stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint Z ξ T hT hξ) hne
end FunctorialResolution.EmbeddedResolution
