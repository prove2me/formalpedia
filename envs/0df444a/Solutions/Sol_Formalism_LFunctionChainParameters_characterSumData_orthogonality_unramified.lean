-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.orthogonality_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:40.56593+00:00
-- url     : https://prove2.me/submissions/75ad3c7b-e57b-4591-ac0c-c7b99dd9ab8f

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_orthogonality_ramified

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
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : OrthoUnram (H := H) := by
  intro D hD p i hp h2 hq hd hi g
  refine (orthogonality_ramified D p i hp hi g).trans ?_
  rw [hD.unram p hp h2 hq hd]
  by_cases hc : i • D.frob p = g
  · subst hc
    simp
  · rw [if_neg hc, if_neg]
    intro hm
    rw [AddSubgroup.mem_bot, sub_eq_zero] at hm
    exact hc hm.symm
end Formalism.LFunctionChainParameters.characterSumData
