-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.divisibility_of_conclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:33.231472+00:00
-- url     : https://prove2.me/submissions/da533f8c-ffdf-4fd7-b142-4bcf45926463

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_ph_eq

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
theorem _root_.solution : DivOfConcl := by
  intro U0 W Top _ m f D C logOm C0 Pl e aP FoP haP hFo hC ha hLa hB hx h u0 u
  have h1 := h u0 u
  unfold ThmConcl at h1
  rw [Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP, ph_eq] at h1
  rw [hFo u0]
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa
  have hY : 0 ≤ (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (Real.rpow_nonneg hx _)
  have h2 := mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)
  have e1 : C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
      = C.cDiv * ((Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)) := by
    unfold Data.nT
    ring
  linarith
end Formalism.LFunctionChainParameters.LBrDiv
