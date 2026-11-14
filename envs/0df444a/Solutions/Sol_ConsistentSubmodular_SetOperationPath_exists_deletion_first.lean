-- Prove2me | solution 1 for ConsistentSubmodular.SetOperationPath.exists_deletion_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:01.150103+00:00
-- url     : https://prove2.me/submissions/6b87f6fe-8159-454b-9146-fb02ab01d98f

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
variable {n : ℕ}
open ConsistentSubmodular.SetOperationPath

theorem solution (A B : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.length = recourse A B ∧ P.node 0 = A ∧
      P.node P.length = B ∧ ∀ i,
        A ∩ B ⊆ P.node i ∧ P.node i ⊆ A ∪ B ∧
          (P.node i).card ≤ max A.card B.card := by
  classical
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path (A ∩ B) (A \ B)
  obtain ⟨R, hRlen, hRinit, hRterm, hRnode⟩ := exists_insertion_path (A ∩ B) (B \ A)
  have hleft : (A ∩ B) ∪ (A \ B) = A := by ext x; simp; tauto
  have hright : (A ∩ B) ∪ (B \ A) = B := by ext x; simp; tauto
  rw [hleft] at hLterm hLnode
  rw [hright] at hRterm hRnode
  have hj : L.reverse.node L.reverse.length = R.node 0 := by simpa [reverse] using hLinit.trans hRinit.symm
  have hlen : (L.reverse.append R hj).length = recourse A B := by
    rw [append_length]
    change L.length + R.length = _
    rw [hLlen, hRlen]
    unfold recourse
    exact (Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro e heA heB
      exact (Finset.mem_sdiff.mp heA).2 (Finset.mem_sdiff.mp heB).1)).symm
  refine ⟨L.reverse.append R hj, hlen, ?_, ?_, ?_⟩
  · simpa using hLterm
  · simpa using (L.reverse.append_terminal R hj).trans hRterm
  · apply L.reverse.append_property R hj
      (fun S => A ∩ B ⊆ S ∧ S ⊆ A ∪ B ∧ S.card ≤ max A.card B.card)
    · intro i
      exact ⟨(hLnode _).1, (hLnode _).2.trans Finset.subset_union_left,
        (Finset.card_le_card (hLnode _).2).trans (le_max_left _ _)⟩
    · intro i
      exact ⟨(hRnode i).1, (hRnode i).2.trans Finset.subset_union_right,
        (Finset.card_le_card (hRnode i).2).trans (le_max_right _ _)⟩

end
