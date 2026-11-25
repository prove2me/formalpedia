-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OrderCertificate.of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:19.80943+00:00
-- url     : https://prove2.me/submissions/55fa298e-d576-4be9-af01-36db8ebea115

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate

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
namespace OrderCertificate
theorem _root_.solution {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) (hmu : 2 ≤ μ) :
    OrderCertificate W p N μ Mem Z :=
  OrderCertificate.large hmu
end OrderCertificate
end FunctorialResolution.EmbeddedResolution
