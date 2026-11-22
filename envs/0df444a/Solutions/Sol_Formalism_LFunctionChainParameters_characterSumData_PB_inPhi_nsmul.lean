-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.inPhi_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:51.539844+00:00
-- url     : https://prove2.me/submissions/0a43a30e-f850-4a02-b94d-4ce68841e1e3

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_add

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
theorem _root_.solution {x : E0 × H} (hx : InPhi x) (i : ℕ) : InPhi (i • x) := by
  induction i with
  | zero => rw [zero_smul]; exact (inPhi_iff _).2 rfl
  | succ n ih => rw [succ_nsmul]; exact inPhi_add ih hx
end Formalism.LFunctionChainParameters.characterSumData.PB
