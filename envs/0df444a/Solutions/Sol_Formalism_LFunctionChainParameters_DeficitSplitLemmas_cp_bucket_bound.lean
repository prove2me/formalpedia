-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.cp_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:24.619689+00:00
-- url     : https://prove2.me/submissions/8b8475bd-c14c-4297-aace-7bb7018355d5

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
theorem _root_.solution : CpBucket := by
  intro C Sk a mT X'' s hC hSk ha hmT hs hcard
  have hla : 0 ≤ Real.log (2 * a) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ 2 * C * Sk * Real.log (2 * a) * mT := by positivity
  simp only [cpF]
  have hterm : ∀ p ∈ s, 2 * Real.log p * (mT * (C * Sk * Real.logb p (2 * a))) ≤
      2 * C * Sk * Real.log (2 * a) * mT := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hs p hp
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    apply le_of_eq
    unfold Real.logb; field_simp
  have h1 := Finset.sum_le_card_nsmul s _ _ hterm
  rw [nsmul_eq_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right hcard hB0
  refine h1.trans (h2.trans (le_of_eq ?_))
  ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
