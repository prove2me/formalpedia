-- Prove2me | solution 1 for Formalism.G0.tops_choice_part_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:47.814688+00:00
-- url     : https://prove2.me/submissions/02b1f1ec-a599-4f6b-b13c-280e7624869a

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartC
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_weight_nonneg
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_bad_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Finset TopsConditionalProbabilityBounds
namespace Formalism.G0
theorem _root_.solution : TopsChoiceThirdBound := by
  intro n δ G hn hδ0 hδ1
  classical
  have hunion : condProb n δ (fun T => ¬ CondC n T G) ≤
      ∑ i ∈ range n, condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) := by
    unfold condProb
    rw [sum_comm]
    apply sum_le_sum
    intro T hT
    rw [mem_powerset] at hT
    split_ifs with h
    · obtain ⟨h0T, hC⟩ := h
      unfold CondC at hC
      push Not at hC
      obtain ⟨i, hiT, hi⟩ := hC
      have hir : i ∈ range n := hT hiT
      refine le_trans (le_of_eq ?_) (single_le_sum ?_ hir)
      · exact (if_pos ⟨h0T, hiT, hi⟩).symm
      · intro j _
        split_ifs
        · exact weight_nonneg n δ hδ0 hδ1 T
        · exact le_rfl
    · apply sum_nonneg
      intro j _
      split_ifs
      · exact weight_nonneg n δ hδ0 hδ1 T
      · exact le_rfl
  calc _ ≤ _ := hunion
    _ ≤ ∑ _i ∈ range n, (1 - δ) ^ G :=
        sum_le_sum (fun i hi => bad_bound n δ G hn hδ0 hδ1 i (mem_range.1 hi))
    _ = n * (1 - δ) ^ G := by rw [sum_const, card_range, nsmul_eq_mul]
end Formalism.G0
