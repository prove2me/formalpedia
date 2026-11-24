-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_le_orderAt_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:19:17.999526+00:00
-- url     : https://prove2.me/submissions/63f9bc32-74f1-40a4-977f-727666a40411

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff


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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    orderAt I (h.base y) ≤ orderAt (I.comap h) y := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_orderAt_iff] at hn ⊢
  rw [stalkIdeal_comap]
  have hmono : Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y))
      ≤ Ideal.map (h.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (h.base y)) ^ n) := Ideal.map_mono hn
  exact le_trans hmono
    (le_trans (Ideal.map_pow ..).le
      (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ..) n))
end FunctorialResolution.EmbeddedResolution
