-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.index_slope_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:24.95606+00:00
-- url     : https://prove2.me/submissions/64f0b796-ed2a-4591-a6a1-0fe0e3fb0cf8

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_index
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muMaxDef_mono


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
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : Formalism.HN.IndexMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX M N hM hNM hN0 hrk
  exact ⟨muDef_index b X hX hM hNM hN0 hrk, muMaxDef_mono b X hX hM hNM hN0⟩
end Formalism.LFunctionChainParameters.LLcv
