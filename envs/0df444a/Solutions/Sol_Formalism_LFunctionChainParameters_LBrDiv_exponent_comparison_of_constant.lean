-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.exponent_comparison_of_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:38.1038+00:00
-- url     : https://prove2.me/submissions/0458d97f-4215-4bfe-a5fa-11b47427d2a5

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : TypePrimeCostOfDeviationBound := by
  intro U0 W Top _ m f D C C0 Pl e aP sE haP hE hC hB h
  have hsum : (∑ t ∈ Finset.univ.map e, aP t) = D.sumA := by
    rw [Finset.sum_map]
    simp only [haP]
    rfl
  constructor
  · intro u0 u j
    have h1 := (h u0 u).1 j
    rw [hsum] at h1
    rw [hE u0 u j]
    exact h1.trans (mul_le_mul_of_nonneg_right hC hB)
  · intro u0 u
    have h1 := (h u0 u).2
    rw [hsum] at h1
    have e1 : D.Ee u0 u = 2 * ∑ j, sE u0 u j := by
      unfold Data.Ee
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hE u0 u j
    rw [e1]
    have e2 : (m : ℝ) * D.sumA * D.lg = (m : ℝ) * (D.sumA * D.lg) := by ring
    rw [e2]
    have hmB : 0 ≤ (m : ℝ) * D.B0 := mul_nonneg (Nat.cast_nonneg _) hB
    calc _ ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * ((m : ℝ) * D.B0) := h1
      _ ≤ C.cE * ((m : ℝ) * D.B0) := mul_le_mul_of_nonneg_right hC hmB
      _ = C.cE * (m : ℝ) * D.B0 := by ring
end Formalism.LFunctionChainParameters.LBrDiv
