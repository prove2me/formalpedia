-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.second_discriminant_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:48.979704+00:00
-- url     : https://prove2.me/submissions/855eaf9b-2ddc-47d8-b543-095235d207b4

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_logdiv_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_second_term_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution : SecondD := by
  intro Ps cand cl Sig θ m T a R hm hT ha hSig hW hcl
  have h1 := second_term_le Ps cand cl Sig θ m T a hm hT ha hcl
  have hc : 0 ≤ 2 * a * m * T := by positivity
  have h2 : ∑ p ∈ cand, (if θ < Sig p then 4 * (m * T * a) * Real.log p / p else 0) ≤
      2 * a * m * T * lhsW cand θ Sig := by
    unfold lhsW
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hl := logdiv_nonneg p
    have hs := hSig p hp
    have h0 : 0 ≤ 2 * a * m * T * (Real.log p / p * (4 * Sig p)) := by positivity
    split_ifs
    · have e : 2 * a * m * T * (Real.log p / p * (2 + 4 * Sig p)) =
          4 * (m * T * a) * Real.log p / p + 2 * a * m * T * (Real.log p / p * (4 * Sig p)) := by ring
      rw [e]; linarith
    · rw [zero_add]; exact h0
  have h3 := mul_le_mul_of_nonneg_left hW hc
  linarith
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
