-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.PB.conj_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:04.965062+00:00
-- url     : https://prove2.me/submissions/b2d49da5-b886-4b2e-9dfb-9eaee2c3cbd7

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible

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
theorem _root_.solution (ψ : AddChar (E0 × H) ℂ) (g : E0 × H) : starRingEnd ℂ (ψ g) = ψ (-g) := by
  first
  | exact (AddChar.map_neg_eq_conj ψ g).symm
  | rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (AddChar.norm_apply ψ g)]
end Formalism.LFunctionChainParameters.characterSumData.PB
