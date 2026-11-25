-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.costM_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:53:58.507273+00:00
-- url     : https://prove2.me/submissions/03081208-9708-459b-91f5-8ad6931cb6d8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_dg_choose


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
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution [NeZero D.r] (hV2 : V2 K) (x : D.ML × Fin D.r) (k : ℕ) :
    CostV (K := K) D.msg Set.univ k (fun ζ => ((ζ x).choose k : K)) :=
  fun _ _ _ _ h => vala_dg_choose hV2 x k h
end Formalism.MainNotions.PlaneGram.TwistData
