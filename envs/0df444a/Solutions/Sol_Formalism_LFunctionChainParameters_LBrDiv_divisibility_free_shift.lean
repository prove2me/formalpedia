-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.divisibility_free_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:32.16416+00:00
-- url     : https://prove2.me/submissions/04e40092-56e4-4434-90bb-68898a720876

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_divisibility_principal_shift

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
theorem _root_.solution : DivFreeShift := by
  intro U0 W Top _ m f D C logOm logOm'
  have key : ∀ u0 (u : W u0),
      (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm) - D.aT t * Real.log (D.T u0 u)))
        = (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * logOm') - D.aT t * Real.log (D.T u0 u)))
          + (m : ℝ) * D.sumA * (logOm' - logOm) := by
    intro u0 u
    have := divisibility_principal_shift Top (m : ℝ) D.aT (Real.log (D.T u0 u)) logOm' logOm
    rw [this]
    unfold Data.sumA
    ring
  constructor
  · intro h u0 u
    have := h u0 u
    rw [key u0 u] at this
    linarith
  · intro h u0 u
    have := h u0 u
    rw [key u0 u]
    linarith
end Formalism.LFunctionChainParameters.LBrDiv
