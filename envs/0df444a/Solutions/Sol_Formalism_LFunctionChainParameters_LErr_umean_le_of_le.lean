-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.umean_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:28.759496+00:00
-- url     : https://prove2.me/submissions/cabddd7f-9bc2-4964-a2bf-96fe2cd0f572

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution {ι : Type} [Fintype ι] (X : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, X i ≤ B) :
    umean X ≤ B := by
  unfold umean
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · rw [h0]; simpa using hB
  · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast h0
    rw [div_le_iff₀ hc]
    calc ∑ i, X i ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => h i)
      _ = B * (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end Formalism.LFunctionChainParameters.LErr
