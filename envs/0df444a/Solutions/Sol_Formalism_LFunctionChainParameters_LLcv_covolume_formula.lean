-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.covolume_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:31.491606+00:00
-- url     : https://prove2.me/submissions/9e0166aa-3f85-4872-8b89-c9a5c4614ae4

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_log_covolume_slope_mu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : Formalism.HN.LcvFormula := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e M he hM hM0 hsp
  obtain ⟨-, -, -, hfin, hmu⟩ := log_covolume_slope_mu K V ι b X hX j e M he hM hM0 hsp
  exact ⟨hfin, hmu⟩
end Formalism.LFunctionChainParameters.LLcv
