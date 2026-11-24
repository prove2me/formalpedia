-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:29.209514+00:00
-- url     : https://prove2.me/submissions/44c2e464-4780-4d35-bfbf-2e7041fcbb0c

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_zetaR_nonneg_le_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (M : ℕ) (hM : 2 ≤ M) : Real.log (zetaR M) ≤ 1 := by
  obtain ⟨h0, h2⟩ := zetaR_nonneg_le_two M hM
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; norm_num
  · calc Real.log (zetaR M) ≤ Real.log 2 := Real.log_le_log h h2
      _ ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
end Formalism.LogVandermondeBounds.StandardLattice
