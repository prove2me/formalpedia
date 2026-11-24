-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.choose_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:23.344+00:00
-- url     : https://prove2.me/submissions/3f2cb718-0ba2-42db-801a-fc10760ba4a8

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
theorem _root_.solution : ChooseWindow := by
  intro Ω _ π X M hπ h1 hM
  by_contra hcon
  push Not at hcon
  have hterm : ∀ o ∈ (Finset.univ : Finset Ω), 0 ≤ π o * (X o - M) := by
    intro o _
    rcases (hπ o).eq_or_lt with h | h
    · rw [← h]; simp
    · exact mul_nonneg h.le (by linarith [hcon o h])
  have hsum : ∑ o, π o * (X o - M) ≤ 0 := by
    have e : ∑ o, π o * (X o - M) = ∑ o, π o * X o - (∑ o, π o) * M := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro o _; ring
    rw [e, h1]; linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
    (le_antisymm hsum (Finset.sum_nonneg hterm))
  have hπ0 : ∀ o, π o = 0 := by
    intro o
    by_contra hne
    have hpos : 0 < π o := lt_of_le_of_ne (hπ o) (Ne.symm hne)
    have h2 := hz o (Finset.mem_univ o)
    have h3 : 0 < π o * (X o - M) := mul_pos hpos (by linarith [hcon o hpos])
    linarith
  simp [hπ0] at h1
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
