-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.index_to_lambda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:38.397391+00:00
-- url     : https://prove2.me/submissions/ef39270b-bf0d-4ce9-aaea-56e0b8e077e6

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered

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
theorem _root_.solution : IndexToLengthBound := by
  intro U0 W Top _ m f D aM VV Wt bt hW
  obtain ⟨hk, hkb, ha, haM, hWt, hbt⟩ := hW
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hb' : 0 ≤ D.b' := by linarith
  have hak : 0 ≤ D.a / D.k := div_nonneg ha hk.le
  have haMk : aM / D.k ≤ 2 * (D.a / D.k) := by
    have := div_le_div_of_nonneg_right haM hk.le
    have e : 2 * D.a / D.k = 2 * (D.a / D.k) := by ring
    linarith
  have hcard : ((VV.card : ℕ) : ℝ) ≤ D.nT := by
    unfold Data.nT
    exact_mod_cast Finset.card_le_univ VV
  have h1 : ∑ t ∈ VV, ((aM / D.k + 2 * Wt t + D.k) + bt t) ≤ ∑ _t ∈ VV, 7 * (D.a / D.k + D.b') :=
    Finset.sum_le_sum (fun t _ => by have := hWt t; have := hbt t; linarith)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib] at h1
  have h2 : ((VV.card : ℕ) : ℝ) * (7 * (D.a / D.k + D.b')) ≤ D.nT * (7 * (D.a / D.k + D.b')) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (le_trans h1 h2) hm
  unfold lambdaIndex
  linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
