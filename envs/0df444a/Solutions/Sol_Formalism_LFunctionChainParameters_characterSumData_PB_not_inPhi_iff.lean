-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.not_inPhi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:28.260083+00:00
-- url     : https://prove2.me/submissions/a7cdfc82-b4ef-4177-8c1d-c03662d62a5d

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_zmod_two_cases_bis
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_iff

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
theorem _root_.solution (g : E0 × H) : ¬ InPhi g ↔ g.1.1 = 1 := by
  rw [inPhi_iff]
  rcases zmod_two_cases_bis g.1.1 with h | h <;> rw [h] <;> decide
end Formalism.LFunctionChainParameters.characterSumData.PB
