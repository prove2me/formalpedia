-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_Ico
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:40.387362+00:00
-- url     : https://prove2.me/submissions/897ba454-2807-44ea-bdb5-1c788e19a19a

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_tail_step

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
theorem _root_.solution (p₀ : ℕ) (hp : 3 ≤ p₀) (K : ℕ) :
    ∑ n ∈ Finset.Ico p₀ (p₀ + K), Real.log n / (n : ℝ) ^ 2 ≤
      2 * (gT ((p₀ : ℝ) - 1) - gT ((p₀ : ℝ) + K - 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h3 : (3 : ℝ) ≤ ((p₀ + K : ℕ) : ℝ) := by
      have : 3 ≤ p₀ + K := by omega
      exact_mod_cast this
    have hs := tail_step ((p₀ + K : ℕ) : ℝ) h3
    push_cast at hs ⊢
    have e : (p₀ : ℝ) + (K + 1) - 1 = p₀ + K := by ring
    rw [e]
    linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
