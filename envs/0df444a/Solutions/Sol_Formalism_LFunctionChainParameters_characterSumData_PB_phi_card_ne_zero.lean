-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.phi_card_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:44.288564+00:00
-- url     : https://prove2.me/submissions/f1c1ea73-016e-451d-b6b3-7c66343ee67e

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
theorem _root_.solution : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  apply Finset.card_ne_zero.mpr
  exact ⟨0, by simp [PhiSet, inPhi_iff]⟩
end Formalism.LFunctionChainParameters.characterSumData.PB
