-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.costM_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:31.663167+00:00
-- url     : https://prove2.me/submissions/8f7dd8c0-6ac2-4f85-96ca-56719b4a3244

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_costV_ok
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_smul


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
theorem _root_.solution : CostOK (CostV (K := K) (r := D.r) D.msg Set.univ) :=
  costV_ok D.msg Set.univ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)
end Formalism.MainNotions.PlaneGram.TwistData
