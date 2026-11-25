-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.joint_discriminant_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:51.301815+00:00
-- url     : https://prove2.me/submissions/66223b92-8d53-49ff-af7f-698a60247564

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_discriminant_windows_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_joint_core

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
theorem _root_.solution : LossBoundsUnderSizeWindows := by
  obtain ⟨Cord, h0, h⟩ := joint_core
  refine ⟨Cord, h0, ?_⟩
  intro P e K hC hW hL ι κ τ U Ps cand PR J TT BAD Sig io D hS
  exact (h (clr P) e K hC ((discriminant_windows_iff P e K).1 hW) hL ι κ τ U Ps cand PR J TT BAD Sig io D hS).2
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
