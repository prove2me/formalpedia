-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.v_elimination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:58.62737+00:00
-- url     : https://prove2.me/submissions/dfad91c2-da51-4c8f-9b00-eae22c7d1db0

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_divisibility_of_free
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_periodicity_solvable
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_free_count_of_count

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
theorem _root_.solution : VElim := by
  intro U0 W Top _ m f D C hw
  constructor
  · rintro ⟨v, hv, hD, hC⟩
    refine ⟨(withV D v).logOm, fun u0 u => hD u0 u, ?_, fun u0 u => ⟨(hC u0 u).2.1, (hC u0 u).2.2⟩⟩
    have h := (free_count_of_count U0 W Top m f (withV D v) C (withV D v).logOm hv hw rfl).mpr
      (fun u0 u => (hC u0 u).1)
    exact h
  · rintro ⟨logOm, h1, h2, h3⟩
    obtain ⟨v, hv, hp⟩ := periodicity_solvable D.gam D.LpL logOm
    refine ⟨v, hv, divisibility_of_free U0 W Top m f (withV D v) C logOm h1 hp, ?_⟩
    intro u0 u
    exact ⟨(free_count_of_count U0 W Top m f (withV D v) C logOm hv hw hp).mp h2 u0 u,
      (h3 u0 u).1, (h3 u0 u).2⟩
end Formalism.LFunctionChainParameters.LBrDiv
