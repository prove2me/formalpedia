-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mul_orderAt_le_orderAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:56.415014+00:00
-- url     : https://prove2.me/submissions/e3633404-eeb8-470c-b89e-924e53438bc4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mul_idealOrder_le_idealOrder_pow


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
theorem _root_.solution (I : X.IdealSheafData) (c : ℕ) (x : X) :
    (c : ℕ∞) * orderAt I x ≤ orderAt (I ^ c) x := by
  rw [orderAt_eq_idealOrder (I ^ c), stalkIdeal_pow]
  exact mul_idealOrder_le_idealOrder_pow (stalkIdeal I x) c
end FunctorialResolution.EmbeddedResolution
