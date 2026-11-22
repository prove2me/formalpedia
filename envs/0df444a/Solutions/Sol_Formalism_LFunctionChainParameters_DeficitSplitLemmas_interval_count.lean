-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.interval_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:50.19525+00:00
-- url     : https://prove2.me/submissions/65aaa2de-2c33-41a2-a73f-8f30d788adc1

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
theorem _root_.solution : IntervalCount := by
  intro A B s hAB hs
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; linarith
  · have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) :=
      fun n hn => Finset.mem_Icc.2 ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hmM : s.min' hne ≤ s.max' hne := s.min'_le_max' hne
    have hc : (s.card : ℝ) ≤ ((Finset.Icc (s.min' hne) (s.max' hne)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.cast_sub (by omega)] at hc
    push_cast at hc
    have hm := (hs _ (s.min'_mem hne)).1
    have hM := (hs _ (s.max'_mem hne)).2
    linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
