-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comapSubscheme_comp_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:32.781487+00:00
-- url     : https://prove2.me/submissions/9147a6a2-188c-4af3-a58c-6b4a719092df

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_CertificateOpenRestriction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_comapSubscheme_comp

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
theorem _root_.solution {V W T : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData)
    (g : W ⟶ T) :
    comapSubscheme f D ≫ D.subschemeι ≫ g = (D.comap f).subschemeι ≫ f ≫ g := by
  rw [← Category.assoc, comapSubscheme_comp, Category.assoc]
end FunctorialResolution.EmbeddedResolution
