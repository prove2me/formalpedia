-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.costM_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:25.728814+00:00
-- url     : https://prove2.me/submissions/05df1382-3f8e-409d-a48e-72a601671eaa

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hV2 : V2 K) (D : TwistData K) (hr : 0 < D.r) (x : D.ML × Fin D.r) (k : ℕ) :
    CostM D k (fun α => ((α x).choose k : K)) := by
  haveI : NeZero D.r := ⟨hr.ne'⟩
  intro S _ θ F h
  exact vala_dg_choose hV2 x k h
end Formalism.MainNotions.PlaneGram
