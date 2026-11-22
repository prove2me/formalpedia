-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.prob_exists_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:32.318482+00:00
-- url     : https://prove2.me/submissions/00cd3837-c2c9-43c3-a8d6-a9d75db05b39

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_w_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution {ι : Type*} {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (s : Finset ι)
    (A : ι → Finset ℕ → Prop) :
    P U δ (fun t => ∃ j ∈ s, A j t) ≤ ∑ j ∈ s, P U δ (A j) := by
  classical
  unfold P
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  have hnn : ∀ j ∈ s, 0 ≤ (if A j t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0) := by
    intro j _
    split_ifs
    · exact w_nonneg h0 h1 _ _
    · exact le_rfl
  by_cases h : ∃ j ∈ s, A j t
  · rw [if_pos h]
    obtain ⟨j, hj, hA⟩ := h
    calc δ ^ t.card * (1 - δ) ^ (U.card - t.card)
        = (if A j t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0) := by rw [if_pos hA]
      _ ≤ _ := single_le_sum (f := fun j => if A j t then
            δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0) hnn hj
  · rw [if_neg h]
    exact sum_nonneg hnn
end Formalism.G0.TopsConditionalProbabilityWindows
