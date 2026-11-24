-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.choose_window_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:38.941076+00:00
-- url     : https://prove2.me/submissions/a97acade-b540-49a0-98ae-4b84b0e0c6e1

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_choose_window

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
theorem _root_.solution : ChooseWindow2 := by
  intro Ω _ π F G A B hπ h1 hF hG hA hB
  obtain ⟨o, ho, hX⟩ := choose_window Ω π (fun o => F o + G o) (A + B) hπ h1 (by
    simp only [mul_add, Finset.sum_add_distrib]; linarith)
  exact ⟨o, ho, hX, by linarith [hG o], by linarith [hF o]⟩
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
