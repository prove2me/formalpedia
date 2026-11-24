-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:31.493131+00:00
-- url     : https://prove2.me/submissions/550115c7-bcb3-4981-97c3-b7857c7eee0f

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution (y : ℝ) (hy : 3 ≤ y) : Real.log y / y ^ 2 ≤ 2 * (gT (y - 1) - gT y) := by
  unfold gT
  have hy1 : 0 < y - 1 := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9; linarith
  have hdiff : Real.log y - Real.log (y - 1) ≤ 1 / (y - 1) := by
    rw [← Real.log_div hy0.ne' hy1.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < y / (y - 1) by positivity)
    have e : y / (y - 1) - 1 = 1 / (y - 1) := by field_simp; ring
    linarith
  set L := Real.log y
  set L1 := Real.log (y - 1)
  have hD1 : (L - L1) * (y - 1) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hdiff hy1.le
    rwa [one_div, inv_mul_cancel₀ hy1.ne'] at this
  have hD2 : L - L1 ≤ 1 / 2 := by
    have : 1 / (y - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hy1 (by norm_num)]; linarith
    linarith
  have hDy : y * (L - L1) ≤ 3 / 2 := by nlinarith
  have hG : L * (y - 1) ≤ 2 * y * (y * (L1 + 1) - (y - 1) * (L + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hDy hy0.le]
  have e2 : 2 * ((L1 + 1) / (y - 1) - (L + 1) / y) =
      2 * (y * (L1 + 1) - (y - 1) * (L + 1)) / (y * (y - 1)) := by
    field_simp
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hG hy0.le
  nlinarith [this]
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
