-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.splitLe_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:37.290051+00:00
-- url     : https://prove2.me/submissions/022cc963-7ff6-49f7-af35-6e6e8fc338df

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_splitEq_valid
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_deficit_le
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_deficit_dropped

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
theorem _root_.solution : SplitLe := by
  intro ι κ τ W below l Ps S J TT TTp vonMangoldtClassSum dT gainW tauW gain tau lo fl h hS hled hdrop
  rw [splitEq_valid ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h,
    ← Finset.sum_sdiff hS]
  have hA : ∑ p ∈ S, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p ≤
      ∑ p ∈ S, 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p := by
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (deficit_le J TT TTp vonMangoldtClassSum gain tau lo fl p (hled p hp))
      (by have := Real.log_natCast_nonneg p; linarith)
  have hB : ∑ p ∈ Ps \ S, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p =
      ∑ p ∈ Ps \ S, 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [deficit_dropped J TT vonMangoldtClassSum gain tau p (hdrop p hp).1 (hdrop p hp).2]
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
