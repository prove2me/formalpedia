-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_weightedSum_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:35.218995+00:00
-- url     : https://prove2.me/submissions/dcab6266-7fa2-432a-9f66-5532200c22e8

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Theorems.Thm_Formalism_ZeroFreeDirichlet_weightedSum_identity
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_sum_Ioc_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖((y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y) - ((Y - y : ℝ) : ℂ) * partialSumUpTo f y‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by
  rw [weightedSum_identity f hyY, add_sub_cancel_left]
  exact norm_sum_Ioc_le f hf hy hyY
end Formalism.ZeroFreeDirichlet
