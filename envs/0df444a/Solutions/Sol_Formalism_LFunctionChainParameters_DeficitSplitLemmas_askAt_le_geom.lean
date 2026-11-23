-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.askAt_le_geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:51.148014+00:00
-- url     : https://prove2.me/submissions/b135241e-4444-4079-92b8-ff33a6744903

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
theorem _root_.solution (I : Finset ℕ) (at_ p : ℝ) (w : ℕ → ℝ) (hp : 0 < p) (ha : 0 ≤ at_)
    (hw : ∀ i ∈ I, 0 ≤ w i) : askAt I at_ p w ≤ at_ * ∑ i ∈ I, (1 / p) ^ i := by
  unfold askAt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have e : at_ * (1 / p) ^ i = at_ / p ^ i := by rw [one_div, inv_pow]; rfl
  rw [e]
  apply max_le
  · linarith [hw i hi]
  · positivity
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
