-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.markov_drop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:28.297899+00:00
-- url     : https://prove2.me/submissions/ffb49ce6-7470-4e31-b792-f9a69736b839

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
theorem _root_.solution : MarkovDrop := by
  intro Ω _ π s Sig L θ s₀ hπ hθ hSig hL hmean
  have h1 : ∑ o, π o * ∑ p ∈ s, (if θ < Sig p o then L p else 0) ≤
      ∑ o, π o * ∑ p ∈ s, (Sig p o / θ * L p) := by
    apply Finset.sum_le_sum
    intro o _
    apply mul_le_mul_of_nonneg_left _ (hπ o)
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with h
    · have : 1 ≤ Sig p o / θ := by rw [le_div_iff₀ hθ]; linarith
      nlinarith [hL p hp]
    · exact mul_nonneg (div_nonneg (hSig p hp o) hθ.le) (hL p hp)
  have h2 : ∑ o, π o * ∑ p ∈ s, (Sig p o / θ * L p) = ∑ p ∈ s, L p / θ * ∑ o, π o * Sig p o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro o _
    ring
  have h3 : ∑ p ∈ s, L p / θ * ∑ o, π o * Sig p o ≤ ∑ p ∈ s, L p / θ * s₀ := by
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hmean p hp) (div_nonneg (hL p hp) hθ.le)
  have h4 : ∑ p ∈ s, L p / θ * s₀ = s₀ / θ * ∑ p ∈ s, L p := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
