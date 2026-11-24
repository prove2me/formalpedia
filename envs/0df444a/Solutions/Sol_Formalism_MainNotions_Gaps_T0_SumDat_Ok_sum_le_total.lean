-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.sum_le_total
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:30.376509+00:00
-- url     : https://prove2.me/submissions/55a2a926-d996-4285-973e-07e754f78506

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_sum_le_named
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_named_le_total

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
theorem _root_.solution (h : X.Ok) {PP : ℝ} (hP : X.Rel PP) :
    ∑ la ∈ X.s, X.rr la * X.l la ≤ X.total PP := (h.sum_le_named).trans (h.named_le_total hP)
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
