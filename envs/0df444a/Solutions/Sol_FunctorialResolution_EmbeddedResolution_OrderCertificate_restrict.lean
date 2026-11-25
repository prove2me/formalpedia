-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OrderCertificate.restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:25.425739+00:00
-- url     : https://prove2.me/submissions/7cf19f37-1a8e-42fd-938f-dac6257db660

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_CertificateOpenRestriction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OrderCertificate_comap_of_isOpenImmersion

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
theorem _root_.solution {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    (hin : OpenImmersionStability k) (U : W.Opens) :
    OrderCertificate U.toScheme (U.ι ≫ p) (N.comap U.ι) μ (U.ι.base ⁻¹' Mem) (Z.comap U.ι) :=
  h.comap_of_isOpenImmersion hin U.ι
end OrderCertificate
end FunctorialResolution.EmbeddedResolution
