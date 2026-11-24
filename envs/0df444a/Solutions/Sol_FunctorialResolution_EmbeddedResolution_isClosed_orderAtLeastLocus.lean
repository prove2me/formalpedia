-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isClosed_orderAtLeastLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:12.917057+00:00
-- url     : https://prove2.me/submissions/faca40b2-befe-4822-b022-85488e2e2398

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_derivIdealSheafIterate_eq_orderAtLeastLocus
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
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (m : ℕ) : IsClosed (orderAtLeastLocus I m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [orderAtLeastLocus_zero]
    exact isClosed_univ
  · have hm1 : 1 ≤ m := by omega
    rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1]
    exact (derivIdealSheafIterate k p (m - 1) I).support.2
end FunctorialResolution.EmbeddedResolution
