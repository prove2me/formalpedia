-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.splitEq_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:40.812561+00:00
-- url     : https://prove2.me/submissions/71782cde-64dc-450e-8784-617b38ffc6dc

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_ga_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_ask_eq

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
theorem _root_.solution : SplitEq := by
  intro ι κ τ W below l Ps J TT vonMangoldtClassSum dT gainW tauW gain tau h
  rw [ask_eq, ga_eq W below l Ps J gainW tauW gain tau h]
  unfold deficit
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
