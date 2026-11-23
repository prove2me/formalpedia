-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.chC_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:05.644947+00:00
-- url     : https://prove2.me/submissions/ebf405be-792c-4b56-a310-9d9a63ca4acb

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData.PB
theorem _root_.solution (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) g * chC g = 1 := by
  rw [chC_apply']
  split_ifs <;> simp
end Formalism.LFunctionChainParameters.characterSumData.PB
