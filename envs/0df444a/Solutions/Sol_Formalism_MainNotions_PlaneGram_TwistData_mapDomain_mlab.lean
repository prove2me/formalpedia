-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.mapDomain_mlab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:45.41914+00:00
-- url     : https://prove2.me/submissions/aec102e6-6d4a-4780-b9af-a4ed03d7ce88

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_localizationToLaurent_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mlab t, a) = α (Sum.inr t, a) :=
  Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inr t, a)
end Formalism.MainNotions.PlaneGram.TwistData
