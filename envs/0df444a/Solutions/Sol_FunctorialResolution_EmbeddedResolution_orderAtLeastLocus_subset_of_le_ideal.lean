-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_of_le_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:21.327996+00:00
-- url     : https://prove2.me/submissions/d6c793c0-08bc-40eb-a885-69362fa7793b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_le_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff

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
theorem _root_.solution {I J : X.IdealSheafData} (h : I ≤ J) (m : ℕ) :
    orderAtLeastLocus J m ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  exact le_trans hx (orderAt_le_of_le h x)
end FunctorialResolution.EmbeddedResolution
