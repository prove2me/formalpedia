-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_insertion_first_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:01.847448+00:00
-- url     : https://prove2.me/submissions/82befa64-b096-4c8c-9929-3d274f9c6e3d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_insertion_path

section

noncomputable section

namespace ConsistentSubmodular

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem append_property (Q : SetOperationPath n) (hjoin)
    (good : Finset (Fin n) → Prop) (hP : ∀ i, good (P.node i))
    (hQ : ∀ i, good (Q.node i)) : ∀ i, good ((P.append Q hjoin).node i) := by
  intro i
  change good (if i ≤ P.length then P.node i else Q.node (i - P.length))
  split
  · exact hP i
  · exact hQ _

end SetOperationPath

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (A B Q : Finset (Fin n)) (V : ℝ)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧
      P.length ≤ A.card + B.card ∧ ∀ j, P.node j ⊆ A ∪ B ∧
        (P.node j).card ≤ A.card + B.card ∧ V ≤ f.value (Q ∪ P.node j) := by
  obtain ⟨L, hLl, hL0, hL1, hL⟩ := SetOperationPath.exists_insertion_path A B
  obtain ⟨R, hRl, hR0, hR1, hR⟩ := SetOperationPath.exists_insertion_path B A
  have hj : L.node L.length = R.reverse.node 0 := by
    rw [SetOperationPath.reverse_initial, hL1, hR1, Finset.union_comm]
  refine ⟨L.append R.reverse hj, by simpa using hL0, ?_, ?_, ?_⟩
  · simpa using (L.append_terminal R.reverse hj).trans (by simpa [SetOperationPath.reverse] using hR0)
  · simp only [SetOperationPath.append_length, SetOperationPath.reverse]
    omega
  · apply L.append_property R.reverse hj
      (fun S => S ⊆ A ∪ B ∧ S.card ≤ A.card + B.card ∧ V ≤ f.value (Q ∪ S))
    · intro j
      refine ⟨(hL j).2, (Finset.card_le_card (hL j).2).trans (Finset.card_union_le _ _), ?_⟩
      exact hA.trans (f.monotone _ _ (Finset.union_subset_union_right (hL j).1))
    · intro j
      have hs : R.reverse.node j ⊆ A ∪ B := by simpa [SetOperationPath.reverse, Finset.union_comm] using (hR (R.length - j)).2
      refine ⟨hs, (Finset.card_le_card hs).trans (Finset.card_union_le _ _), ?_⟩
      exact hB.trans (f.monotone _ _ (Finset.union_subset_union_right (hR (R.length - j)).1))

end
