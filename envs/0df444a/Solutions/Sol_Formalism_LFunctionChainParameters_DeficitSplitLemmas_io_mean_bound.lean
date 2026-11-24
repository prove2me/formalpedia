-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.io_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:30.121221+00:00
-- url     : https://prove2.me/submissions/bf2d1db1-daaf-4f69-a43f-e5409914e709

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_prime_log_sum_bound

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
theorem _root_.solution : IoMean := by
  intro Ω _ π s Sig io Y s₀ mTa hπ hs₀ hm hY hs hmean hio
  have h1 : ∑ o, π o * ∑ p ∈ s, Real.log p * io p o ≤
      ∑ o, π o * ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) := by
    apply Finset.sum_le_sum
    intro o _
    apply mul_le_mul_of_nonneg_left _ (hπ o)
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hio p hp o) (Real.log_natCast_nonneg p)
  have h2 : ∑ o, π o * ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) =
      ∑ p ∈ s, 4 * mTa * (Real.log p / p) * ∑ o, π o * Sig p o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro o _
    ring
  have h3 : ∑ p ∈ s, 4 * mTa * (Real.log p / p) * ∑ o, π o * Sig p o ≤
      ∑ p ∈ s, 4 * mTa * (Real.log p / p) * s₀ := by
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left (hmean p hp)
    exact mul_nonneg (by linarith) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have h4 : ∑ p ∈ s, 4 * mTa * (Real.log p / p) * s₀ = 4 * mTa * s₀ * ∑ p ∈ s, Real.log p / p := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  have h5 := mul_le_mul_of_nonneg_left (prime_log_sum_bound Y s hY hs)
    (show 0 ≤ 4 * mTa * s₀ by positivity)
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
