-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.named_le_total
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:12.040863+00:00
-- url     : https://prove2.me/submissions/adb255d6-f7de-4994-97fd-2b3cdd66d710

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_total_le_of_bounds
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_d0

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
theorem _root_.solution (h : X.Ok) {PP : ℝ} (hP : X.Rel PP) : X.totalNamed ≤ X.total PP := by
  unfold SumDat.totalNamed SumDat.total
  exact total_le_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ h.d0 (by linarith [h.T1]) h.c0 h.κ0 h.γ0 hP.r1 hP.r2 hP.r3 hP.r4
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
