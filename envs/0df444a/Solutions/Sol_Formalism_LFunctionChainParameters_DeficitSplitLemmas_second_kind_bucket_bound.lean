-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.second_kind_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:34.013382+00:00
-- url     : https://prove2.me/submissions/7b7f86ee-b62d-45ce-866f-a02c1ed1824a

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_prime_log_sum_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_markov_drop

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
theorem _root_.solution : SecondKindBucket := by
  intro Ω _ π s Sig Y θ s₀ mTa hπ hθ hs₀ hm hY hSig hs hmean
  have h1 := markov_drop Ω π s Sig (fun p => 4 * mTa * Real.log p / p) θ s₀ hπ hθ hSig
    (fun p _ => div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p))
    hmean
  refine h1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hs₀ hθ.le)
  have e : ∑ p ∈ s, 4 * mTa * Real.log p / p = 4 * mTa * ∑ p ∈ s, Real.log p / p := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (prime_log_sum_bound Y s hY hs) (by linarith)
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
