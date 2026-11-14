-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_rounded_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:14.715449+00:00
-- url     : https://prove2.me/submissions/a1a59456-78a9-4492-83ae-0ffe63c060c0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeRounding
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_deletion_first
import Theorems.Thm_ConsistentSubmodular_Objective_exists_insertion_first_bridge
import Theorems.Thm_ConsistentSubmodular_Objective_exists_rounded_bridge_large

section

noncomputable section

namespace ConsistentSubmodular

namespace Objective

variable {n : ℕ} (f : Objective n)

theorem exists_zero_bridge (A B Q : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧
      P.length ≤ A.card + B.card ∧ ∀ j, P.node j ⊆ A ∪ B ∧
        (P.node j).card ≤ max A.card B.card ∧ 0 ≤ f.value (Q ∪ P.node j) := by
  obtain ⟨P, hl, h0, h1, hn⟩ := SetOperationPath.exists_deletion_first A B
  refine ⟨P, h0, h1, ?_, fun j => ⟨(hn j).2.1, (hn j).2.2, f.nonnegative _⟩⟩
  rw [hl]
  unfold recourse
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset))

end Objective

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
set_option maxHeartbeats 2000000
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (A B Q : Finset (Fin n)) (N κ : ℕ) (V : ℝ)
    (hN : 0 < N) (hV : 0 ≤ V)
    (hAc : A.card ≤ κ) (hBc : B.card ≤ κ) (hAv : f.value A ≤ V) (hBv : f.value B ≤ V)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧ P.length ≤ 10 * κ ∧
      ∀ j, P.node j ⊆ A ∪ B ∧ ((P.node j).card : ℝ) ≤ κ + (κ : ℝ) / N + bridgeHeavy N ∧
        ((3 : ℝ) / 4 - 2 / N) * V ≤ f.value (Q ∪ P.node j) := by
  by_cases hV0 : V = 0
  · obtain ⟨P, h0, h1, hlen, hnode⟩ := f.exists_zero_bridge A B Q
    refine ⟨P, h0, h1, by omega, ?_⟩
    intro j
    refine ⟨(hnode j).1, ?_, ?_⟩
    · have hc : ((P.node j).card : ℝ) ≤ κ :=
        Nat.cast_le.mpr ((hnode j).2.1.trans (max_le hAc hBc))
      have hdiv : (0 : ℝ) ≤ (κ : ℝ) / N := by positivity
      have hH : (0 : ℝ) ≤ bridgeHeavy N := Nat.cast_nonneg _
      linarith
    · simpa [hV0] using (hnode j).2.2
  · by_cases hκ : bridgeHeavy N ≤ κ
    · exact f.exists_rounded_bridge_large A B Q N κ V hN hκ (lt_of_le_of_ne hV (Ne.symm hV0))
        hAc hBc hAv hBv hA hB
    · obtain ⟨P, h0, h1, hlen, hnode⟩ := f.exists_insertion_first_bridge A B Q V hA hB
      refine ⟨P, h0, h1, by omega, ?_⟩
      intro j
      refine ⟨(hnode j).1, ?_, ?_⟩
      · have hc : ((P.node j).card : ℝ) ≤ κ + bridgeHeavy N := by
          exact_mod_cast (show (P.node j).card ≤ κ + bridgeHeavy N by have := (hnode j).2.1; omega)
        have hdiv : (0 : ℝ) ≤ (κ : ℝ) / N := by positivity
        linarith
      · have hdiv : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
        have hh := mul_nonneg hdiv hV
        nlinarith [(hnode j).2.2]

end
