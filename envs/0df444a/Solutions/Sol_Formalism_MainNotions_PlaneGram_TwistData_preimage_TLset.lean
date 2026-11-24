-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.preimage_TLset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:34.776395+00:00
-- url     : https://prove2.me/submissions/20a08831-724a-469f-ab55-2452de18c84b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin

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
theorem _root_.solution (j : Fin D.J) (m : Fin D.r) :
    (D.TLset j m).preimage D.iotaL D.iotaL_injective.injOn = D.Tset j m := by
  ext x
  rw [Finset.mem_preimage]
  rcases x with b | t
  · simp [iotaL, TLset, Tset, mb, mlab]
  · simp [iotaL, TLset, Tset, mb, mlab]
end Formalism.MainNotions.PlaneGram.TwistData
