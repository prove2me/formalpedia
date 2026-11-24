-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.card_notPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:34.461047+00:00
-- url     : https://prove2.me/submissions/bd5a3d76-669a-42c2-94d4-e540768b0f5e

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_sum_partner

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
theorem _root_.solution : (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = (PhiSet (H := H)).card := by
  have h := sum_partner (H := H) (β := ℕ) 0 (fun _ => 1)
  simpa using h
end Formalism.LFunctionChainParameters.characterSumData.PB
