-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_derivIdealSheafIterate_eq_orderAtLeastLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:49:40.929807+00:00
-- url     : https://prove2.me/submissions/d80e246c-3309-4452-8360-687fa7046b05

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_one_iff


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
theorem _root_.solution (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) :
    ((derivIdealSheafIterate k p (m - 1) I).support : Set X) = orderAtLeastLocus I m := by
  have h1 : m - 1 < m := by omega
  have h2 : m - (m - 1) = 1 := by omega
  have h3 := orderAtLeastLocus_derivIdealSheafIterate k p I (r := m - 1) (m := m) h1
  rw [h2] at h3
  rw [← h3]
  ext x
  exact (mem_orderAtLeastLocus_one_iff (derivIdealSheafIterate k p (m - 1) I) x).symm
end FunctorialResolution.EmbeddedResolution
