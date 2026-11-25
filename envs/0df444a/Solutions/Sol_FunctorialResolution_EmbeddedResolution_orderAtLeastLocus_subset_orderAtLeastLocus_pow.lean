-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_orderAtLeastLocus_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:26.179851+00:00
-- url     : https://prove2.me/submissions/b11f20d2-ecd2-4d32-b340-9c744bb4b65a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mul_orderAt_le_orderAt_pow
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
theorem _root_.solution (I : X.IdealSheafData) (c m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (I ^ c) (c * m) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  calc ((c * m : ℕ) : ℕ∞) = (c : ℕ∞) * (m : ℕ∞) := by push_cast; ring
    _ ≤ (c : ℕ∞) * orderAt I x := by gcongr
    _ ≤ orderAt (I ^ c) x := mul_orderAt_le_orderAt_pow I c x
end FunctorialResolution.EmbeddedResolution
