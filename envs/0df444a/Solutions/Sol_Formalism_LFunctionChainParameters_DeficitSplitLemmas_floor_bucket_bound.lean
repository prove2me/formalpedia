-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.floor_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:27.266107+00:00
-- url     : https://prove2.me/submissions/6746856a-c613-48bd-a61c-2fcf96f7c078

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
theorem _root_.solution : FloorBucket := by
  intro C f N a X'' s hC hf ha hs hcard
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hB0 : 0 ≤ 2 * C * f * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2) := by positivity
  simp only [flF]
  have hterm : ∀ p ∈ s,
      2 * Real.log p * (C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2) ≤
      2 * C * f * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hs p hp
    have hl2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hl2' := Real.log_two_gt_d9
    have hlp : 0 < Real.log p := by linarith
    have e : 2 * Real.log p * (C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2) =
        2 * C * f * (N ^ 2 * Real.log a + Real.log a ^ 2 / Real.log p) := by
      unfold Real.logb; field_simp
    rw [e]
    have h1 : Real.log a ^ 2 / Real.log p ≤ 2 * Real.log a ^ 2 := by
      rw [div_le_iff₀ hlp]
      have : 0 ≤ Real.log a ^ 2 := sq_nonneg _
      nlinarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h1 := Finset.sum_le_card_nsmul s _ _ hterm
  rw [nsmul_eq_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right hcard hB0
  refine h1.trans (h2.trans (le_of_eq ?_))
  ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
