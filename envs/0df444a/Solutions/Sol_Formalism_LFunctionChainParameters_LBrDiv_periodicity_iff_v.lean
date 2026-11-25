-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.periodicity_iff_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:15.768847+00:00
-- url     : https://prove2.me/submissions/d4f9726d-6aec-453b-a59e-aa001c6a1f70

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
theorem _root_.solution : PerIffV := by
  intro U0 W Top m f D logOm hv
  unfold Per
  rw [Real.log_div Real.pi_pos.ne' hv.ne']
  constructor
  · intro h
    have h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm) := by linarith
    calc D.v = Real.exp (Real.log D.v) := (Real.exp_log hv).symm
      _ = Real.pi * Real.exp (D.gam - D.LpL - logOm) := by
        rw [h1, Real.exp_add, Real.exp_log Real.pi_pos]
  · intro h
    have h1 : Real.log D.v = Real.log Real.pi + (D.gam - D.LpL - logOm) := by
      rw [h, Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith
end Formalism.LFunctionChainParameters.LBrDiv
