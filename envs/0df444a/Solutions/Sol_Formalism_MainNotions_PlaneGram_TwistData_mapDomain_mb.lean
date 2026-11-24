-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.mapDomain_mb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:43.638323+00:00
-- url     : https://prove2.me/submissions/0872e38b-6ed4-4476-89c2-ce8e1301d157

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
theorem _root_.solution (α : D.EA) (b : D.Lb) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mb b, a) = α (Sum.inl b, a) :=
  Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inl b, a)
end Formalism.MainNotions.PlaneGram.TwistData
