-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.Ok.tsum_le_page
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:39.362585+00:00
-- url     : https://prove2.me/submissions/f88c9b2a-35af-4bce-a9bb-cb829a2e15f6

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_sum_le_page

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
    (hp : X.Page PP C k b m δ₂ q DF) (h0 : ∀ la ∉ X.s, X.rr la * X.l la = 0) :
    Summable (fun la => X.rr la * X.l la) ∧ ∑' la, X.rr la * X.l la ≤ X.d * X.f * m * b * δ₂ := by
  refine ⟨summable_of_ne_finset_zero h0, ?_⟩
  rw [tsum_eq_sum h0]
  exact h.sum_le_page hP hp
end Ok
end Formalism.MainNotions.Gaps.T0.SumDat
