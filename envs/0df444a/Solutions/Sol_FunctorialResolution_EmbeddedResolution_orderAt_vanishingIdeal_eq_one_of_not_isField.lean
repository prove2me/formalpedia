-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one_of_not_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:24:01.355569+00:00
-- url     : https://prove2.me/submissions/3790dd70-9b28-4c0b-be05-8da13b77b573

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_vanishingIdeal_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem maximalIdeal_ne_bot_of_not_isField {R : Type*} [CommRing R] [IsLocalRing R]
    (h : ¬ IsField R) : IsLocalRing.maximalIdeal R ≠ ⊥ :=
  fun hb => h (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hb)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [IsLocallyNoetherian X]
    (Z : TopologicalSpace.Closeds X) (ξ : X) (T : Set X)
    (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hfield : ¬ IsField (X.presheaf.stalk ξ)) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 :=
  orderAt_vanishingIdeal_eq_one Z ξ T hT hξ (maximalIdeal_ne_bot_of_not_isField hfield)
end FunctorialResolution.EmbeddedResolution
