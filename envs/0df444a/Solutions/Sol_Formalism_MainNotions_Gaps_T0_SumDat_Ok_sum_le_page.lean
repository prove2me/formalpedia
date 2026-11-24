-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.sum_le_page
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:57.416373+00:00
-- url     : https://prove2.me/submissions/72fdde78-e4d6-4b6f-bc72-42c04d32e402

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_sum_le_total
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_total_le_page

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Formalism.MainNotions.Gaps.T0.SumDat
variable {ι : Type*} (X : SumDat ι)
variable {X}
namespace Formalism.MainNotions.Gaps.T0.SumDat
namespace Ok
theorem _root_.solution (h : X.Ok) {PP C k b m δ₂ q DF : ℝ} (hP : X.Rel PP)
    (hp : X.Page PP C k b m δ₂ q DF) :
    ∑ la ∈ X.s, X.rr la * X.l la ≤ X.d * X.f * m * b * δ₂ := (h.sum_le_total hP).trans (h.total_le_page hp)
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
