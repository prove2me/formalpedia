-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.split_classes_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:24.861222+00:00
-- url     : https://prove2.me/submissions/ba74ced6-4320-42b6-95ce-1920509f4b1e

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
theorem _root_.solution : SplitClasses := by
  intro ι κ τ W below l Ps cl J TT TTp vonMangoldtClassSum dT gainW tauW gain tau lo fl h hled hdrop
  rw [splitEq_valid ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ p ∈ Ps, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p ≤
      ((if cl p = PClass.served then 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p else 0) +
      (if cl p = PClass.first then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0) +
      (if cl p = PClass.second then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0) +
      (if cl p = PClass.high then 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p else 0)) := by
    intro p hp
    have hl : 0 ≤ 2 * Real.log p := by have := Real.log_natCast_nonneg p; linarith
    cases hc : cl p with
    | served =>
      simp only [if_true, if_false, reduceCtorEq, add_zero]
      exact mul_le_mul_of_nonneg_left (deficit_le J TT TTp vonMangoldtClassSum gain tau lo fl p (hled p hp hc)) hl
    | first =>
      obtain ⟨hg, ht⟩ := hdrop p hp (by simp [hc])
      rw [deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]
      simp
    | second =>
      obtain ⟨hg, ht⟩ := hdrop p hp (by simp [hc])
      rw [deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]
      simp
    | high =>
      obtain ⟨hg, ht⟩ := hdrop p hp (by simp [hc])
      rw [deficit_dropped J TT vonMangoldtClassSum gain tau p hg ht]
      simp
  have := Finset.sum_le_sum key
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
