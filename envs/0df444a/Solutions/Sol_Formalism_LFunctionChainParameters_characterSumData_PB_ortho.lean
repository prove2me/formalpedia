-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:49.000432+00:00
-- url     : https://prove2.me/submissions/7e9fdd00-fdbe-4709-bd76-a2f95a749431

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_conj_eq_neg

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
theorem _root_.solution (g h : E0 × H) :
    ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ψ h
      = if h = g then (Fintype.card (E0 × H) : ℂ) else 0 := by
  simp_rw [conj_eq_neg, ← AddChar.map_add_eq_mul]
  rw [AddChar.sum_apply_eq_ite]
  simp only [neg_add_eq_sub, sub_eq_zero]
end Formalism.LFunctionChainParameters.characterSumData.PB
