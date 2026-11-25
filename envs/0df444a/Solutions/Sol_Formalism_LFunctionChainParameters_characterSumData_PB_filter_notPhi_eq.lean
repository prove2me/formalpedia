-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.filter_notPhi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:14:59.130033+00:00
-- url     : https://prove2.me/submissions/873ae77e-c12d-4c61-a638-45596a426548

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
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
theorem _root_.solution (t : H) :
    (univ.filter (fun g : E0 × H => ¬ InPhi g)) = univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)) := by
  ext g
  simp [inPhi_iff, topPl]
end Formalism.LFunctionChainParameters.characterSumData.PB
