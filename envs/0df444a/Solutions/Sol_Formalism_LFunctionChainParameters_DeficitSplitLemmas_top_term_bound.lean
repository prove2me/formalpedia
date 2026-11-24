-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.top_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:41.108025+00:00
-- url     : https://prove2.me/submissions/065f95ee-ad14-4340-8d0d-48a88395c883

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_askAt_le_geom
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_geom_odd

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
theorem _root_.solution : AskUpperBound := by
  intro I at_ p w hp ha hw hI
  have hp0 : 0 < p := by linarith
  have h1 := askAt_le_geom I at_ p w hp0 ha hw
  have hq : 1 / p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have h2 := geom_odd I (1 / p) (by positivity) hq hI
  have h3 := mul_le_mul_of_nonneg_left h2 ha
  have e : at_ * (4 / 3 * (1 / p)) = 4 / 3 * at_ / p := by ring
  rw [e] at h3
  exact h1.trans h3
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
