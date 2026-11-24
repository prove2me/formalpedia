-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_map_eq_of_comp_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:38:34.536869+00:00
-- url     : https://prove2.me/submissions/06d61ecb-4c07-40cd-9b60-4ab2ccf28c1e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_OrderUnderStalkIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_maximalIdeal_le_maximalIdeal_of_retraction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_idealOrder_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : g.comp f = RingHom.id R) (hfg : f.comp g = RingHom.id S) (I : Ideal R) :
    idealOrder (Ideal.map f I) = idealOrder I := by
  have hf := map_maximalIdeal_le_maximalIdeal_of_retraction f g hgf
  have hg := map_maximalIdeal_le_maximalIdeal_of_retraction g f hfg
  have h1 := idealOrder_le_idealOrder_map f hf I
  have h3 := idealOrder_le_idealOrder_map g hg (Ideal.map f I)
  rw [Ideal.map_map, hgf, Ideal.map_id] at h3
  exact le_antisymm h3 h1
end FunctorialResolution.EmbeddedResolution
