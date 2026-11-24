-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.chC_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:48.132453+00:00
-- url     : https://prove2.me/submissions/dbf1f643-bc21-4478-a5ad-b954b625c76a

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
theorem _root_.solution (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) (-g) = chC g := by
  have h1 : (-g).1.1 = g.1.1 := by
    simp only [Prod.fst_neg]
    generalize g.1.1 = e
    revert e
    decide
  rw [chC_apply', chC_apply', h1]
end Formalism.LFunctionChainParameters.characterSumData.PB
