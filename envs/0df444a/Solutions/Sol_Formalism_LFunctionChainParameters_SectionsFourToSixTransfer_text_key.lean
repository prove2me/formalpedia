-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.text_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:10.194516+00:00
-- url     : https://prove2.me/submissions/40c4f031-c191-4cf4-a2d2-2ca2aac3bd99

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_text_sizes_windows


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution (ε E : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    8 ≤ x ∧ Real.log (bTx x ε) = x ^ ε ∧ 0 < bTx x ε ∧ 0 < aTx x ε ∧ 0 < bpTx x ε ∧
    ∀ K : ℝ, 0 < K → K ≤ x ^ E → K ≤ aTx x ε ∧ K * bpTx x ε ≤ aTx x ε ∧ x * K ≤ bpTx x ε := by
  obtain ⟨x₀, h⟩ := text_sizes_windows ε E hε
  refine ⟨max x₀ 8, fun x hx => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hxp : 0 < x := by linarith
  have hb : 0 < bTx x ε := Real.exp_pos _
  have ha : 0 < aTx x ε := mul_pos hxp hb
  have hbp : 0 < bpTx x ε := div_pos ha (Real.exp_pos _)
  have hl : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  refine ⟨hx8, hl, hb, ha, hbp, fun K hK hKE => ?_⟩
  obtain ⟨_, _, _, _, k1, _, k2, _, k3⟩ :=
    h x K K 0 hx0 hK hKE hK hKE (Real.rpow_nonneg hxp.le _)
  refine ⟨k1, k2, ?_⟩
  have hxK : 0 < x * K := mul_pos hxp hK
  have hw : 0 < wppTx x ε K := div_pos hbp hxK
  unfold XppTx at k3
  rw [div_le_iff₀ hw] at k3
  have h1 : 1 ≤ wppTx x ε K := by
    by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_mul_of_pos_left hlt ha
    linarith
  unfold wppTx at h1
  rwa [le_div_iff₀ hxK, one_mul] at h1
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
