-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.sigma_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:30.511801+00:00
-- url     : https://prove2.me/submissions/a74b629d-183d-4ea1-b969-75b69056838d

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
theorem _root_.solution : SigMean := by
  intro Ω ν _ π V kap N m T c hm hc hmean hN
  have h1 : ∑ o, π o * (m * ∑ v ∈ V, kap v o) = m * ∑ v ∈ V, ∑ o, π o * kap v o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    apply Finset.sum_congr rfl; intro o _
    ring
  have h2 : ∑ v ∈ V, ∑ o, π o * kap v o ≤ ∑ v ∈ V, N v * c := Finset.sum_le_sum hmean
  rw [← Finset.sum_mul] at h2
  have h3 : (∑ v ∈ V, N v) * c ≤ T * c := mul_le_mul_of_nonneg_right hN hc
  rw [h1]
  have := mul_le_mul_of_nonneg_left (h2.trans h3) hm
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
