-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:46.462864+00:00
-- url     : https://prove2.me/submissions/4aed7ab9-51a2-4d2d-91c8-a12451ecadef

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_add_orderAt_le_orderAt_mul
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
theorem _root_.solution (I J : X.IdealSheafData) (m m' : ℕ) :
    orderAtLeastLocus I m ∩ orderAtLeastLocus J m' ⊆ orderAtLeastLocus (I * J) (m + m') := by
  rintro x ⟨hx, hx'⟩
  rw [mem_orderAtLeastLocus_iff] at hx hx' ⊢
  calc ((m + m' : ℕ) : ℕ∞) = (m : ℕ∞) + (m' : ℕ∞) := by push_cast; ring
    _ ≤ orderAt I x + orderAt J x := add_le_add hx hx'
    _ ≤ orderAt (I * J) x := add_orderAt_le_orderAt_mul I J x
end FunctorialResolution.EmbeddedResolution
