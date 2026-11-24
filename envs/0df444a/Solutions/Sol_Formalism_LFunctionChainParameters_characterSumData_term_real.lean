-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.term_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:46.93784+00:00
-- url     : https://prove2.me/submissions/434abe2a-7c42-4e95-906f-96e8fcfb1cbb

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
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution (a w : ℝ) (hw : w ≠ 0) (n : ℕ) : a / n - w = w * (a / w / n - 1) := by
  have hw' : w * (a / w) = a := by
    first
    | field_simp
    | rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hw, mul_one]
  rw [mul_sub, mul_one, mul_div_assoc', hw']
end Formalism.LFunctionChainParameters.characterSumData
