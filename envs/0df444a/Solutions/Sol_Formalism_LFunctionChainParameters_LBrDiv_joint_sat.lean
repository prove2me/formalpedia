-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.joint_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:17:26.433676+00:00
-- url     : https://prove2.me/submissions/c6b0ab2a-de59-4537-a1b6-1e81e57e2232

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
theorem _root_.solution :
    ParHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε)) (Fintype.card (Fin 1) : ℝ) ∧
    StepHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε))
      (Finset.univ.map (Function.Embedding.refl (Fin 1))) (fun _ => 0) () () satSt ∧
    Per satD 1 ∧ 0 < satD.v ∧ satC.cDiv = 50 * satP.C0 + 10 ∧ satD.Fo () = 2 * satSt.FoP := by
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ParHyp, satD, satP, satC]
    norm_num
    repeat' apply And.intro
    all_goals linarith
  · simp only [StepHyp, satD, satP, satC, satSt, Formalism.LatticeIndexTer.ph]
    norm_num
    repeat' apply And.intro
    all_goals linarith
  · simp only [Per, satD]
    rw [Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne',
      Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  · exact mul_pos Real.pi_pos (Real.exp_pos _)
  · simp only [satC, satP]; norm_num
  · simp only [satD, satSt]; norm_num
end Formalism.LFunctionChainParameters.LBrDiv
