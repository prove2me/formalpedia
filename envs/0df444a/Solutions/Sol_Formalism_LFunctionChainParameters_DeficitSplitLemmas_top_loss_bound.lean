-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.top_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:27.735807+00:00
-- url     : https://prove2.me/submissions/709f4f03-bdef-4c4d-ac4b-2f9f7fd303ae

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_top_term_bound

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
theorem _root_.solution : TopLoss := by
  intro I a at_ p w hp ha hat hw hI
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 := top_term_bound I at_ p w hpR ha hw hI
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h2 : 4 / 3 * at_ / p ≤ 2 * a / p := by
    apply div_le_div_of_nonneg_right _ hp0.le
    linarith
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 2 * Real.log p by linarith)
  have e : 2 * Real.log p * (2 * a / p) = 4 * a * Real.log p / p := by ring
  rw [e] at h3
  exact h3
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
