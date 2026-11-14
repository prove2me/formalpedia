-- Prove2me | solution 1 for ConsistentSubmodular.SetOperationPath.exists_insertion_path
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:57.929201+00:00
-- url     : https://prove2.me/submissions/7bfeaaf0-d191-4cf9-8e89-79974ca875c5

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath

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

theorem solution (A C : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.length = C.card ∧ P.node 0 = A ∧
      P.node P.length = A ∪ C ∧ ∀ i, A ⊆ P.node i ∧ P.node i ⊆ A ∪ C := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    refine ⟨constant A, by rfl, rfl, by simp [constant], ?_⟩
    intro i
    simp [constant]
  | @insert e C he ih =>
    obtain ⟨P, hlen, hinit, hterm, hnode⟩ := ih
    have hs : recourse (insert e (A ∪ C)) (A ∪ C) ≤ 1 := by
      unfold recourse
      have hsub : (insert e (A ∪ C) \ (A ∪ C)) ∪ ((A ∪ C) \ insert e (A ∪ C)) ⊆ {e} := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_singleton] at *
        tauto
      exact (Finset.card_le_card hsub).trans (by simp)
    let Q := oneStep (A ∪ C) (insert e (A ∪ C)) hs
    have hj : P.node P.length = Q.node 0 := by simpa [Q, oneStep] using hterm
    refine ⟨P.append Q hj, ?_, ?_, ?_, ?_⟩
    · simp [hlen, Q, oneStep, Finset.card_insert_of_notMem he]
    · simpa using hinit
    · simpa [Q, oneStep, Finset.union_insert] using P.append_terminal Q hj
    · apply P.append_property Q hj (fun S => A ⊆ S ∧ S ⊆ A ∪ insert e C)
      · intro i
        exact ⟨(hnode i).1, (hnode i).2.trans (by intro x hx; simp at *; tauto)⟩
      · intro i
        change A ⊆ (if i = 0 then A ∪ C else insert e (A ∪ C)) ∧
          (if i = 0 then A ∪ C else insert e (A ∪ C)) ⊆ A ∪ insert e C
        split_ifs <;> constructor <;> intro x hx <;> simp at * <;> tauto

end
