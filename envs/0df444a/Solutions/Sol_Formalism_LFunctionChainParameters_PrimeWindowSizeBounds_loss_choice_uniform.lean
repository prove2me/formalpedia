-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.loss_choice_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:19.108236+00:00
-- url     : https://prove2.me/submissions/c3c49fb6-38ab-42f6-a5d3-83689cf45740

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_loss_choice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : LossChoiceU := by
  intro Ω U _ π Loss s Sig io D Y θ s₀ mTa h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain ⟨o, a1, a2, a3⟩ := loss_choice Ω π
    (fun o => 0 + ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0)) s Sig
    (fun p o => 2 * Sig p o * (2 * mTa / p)) 0 Y θ s₀ mTa
    h1 h2 h3 h4 h5 h6 h7 h8 h9 (fun o => le_refl _) (fun p _ o => le_refl _)
  refine ⟨o, a1, fun υ => ?_, fun υ => le_trans ?_ a3⟩
  · have := h10 υ o
    linarith
  · exact Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_left (h11 υ p hp o) (Real.log_natCast_nonneg p))
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
