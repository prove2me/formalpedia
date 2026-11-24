-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:56.634686+00:00
-- url     : https://prove2.me/submissions/bf1a7e43-93c3-4a0d-9204-45412614fdba

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (I : X.IdealSheafData) (r m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) := by
  rcases Nat.lt_or_ge m r with h | h
  · rw [show m - r = 0 from Nat.sub_eq_zero_of_le (le_of_lt h), orderAtLeastLocus_zero]
    exact Set.subset_univ _
  · intro x hx
    rw [mem_orderAtLeastLocus_iff] at hx ⊢
    refine le_orderAt_derivIdealSheafIterate k p I x (m - r) r ?_
    rw [Nat.sub_add_cancel h]
    exact hx
end FunctorialResolution.EmbeddedResolution
