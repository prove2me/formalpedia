-- Prove2me | solution 1 for ConsistentSubmodular.SetOperationPath.exists_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:43.670236+00:00
-- url     : https://prove2.me/submissions/99780582-1fed-41a2-a1a7-fd033e8d152d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_deletion_first

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
open scoped BigOperators

theorem solution (S : ℕ → Finset (Fin n)) (m B : ℕ) (U : Finset (Fin n))
    (good : Finset (Fin n) → Prop)
    (hmono : ∀ A B, A ⊆ B → good A → good B)
    (hstart : good (S 0))
    (hnodes : ∀ i, i ≤ m → S i ⊆ U ∧ (S i).card ≤ B)
    (hinter : ∀ i, i < m → good (S i ∩ S (i + 1))) :
    ∃ P : SetOperationPath n,
      P.length = ∑ i ∈ Finset.range m, recourse (S i) (S (i + 1)) ∧
      P.node 0 = S 0 ∧ P.node P.length = S m ∧
      ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i) := by
  induction m with
  | zero =>
    refine ⟨constant (S 0), by simp [constant], rfl, rfl, ?_⟩
    intro i
    exact ⟨(hnodes 0 (by omega)).1, (hnodes 0 (by omega)).2, hstart⟩
  | succ m ih =>
    obtain ⟨P, hlen, hinit, hterm, hnode⟩ := ih
      (fun i hi => hnodes i (by omega)) (fun i hi => hinter i (by omega))
    obtain ⟨Q, hQlen, hQinit, hQterm, hQnode⟩ := exists_deletion_first (S m) (S (m + 1))
    have hj : P.node P.length = Q.node 0 := hterm.trans hQinit.symm
    refine ⟨P.append Q hj, ?_, ?_, ?_, ?_⟩
    · simp only [append_length, hlen, hQlen, Finset.sum_range_succ]
    · simpa using hinit
    · simpa using (P.append_terminal Q hj).trans hQterm
    · apply P.append_property Q hj (fun A => A ⊆ U ∧ A.card ≤ B ∧ good A) hnode
      intro i
      exact ⟨(hQnode i).2.1.trans (Finset.union_subset (hnodes m (by omega)).1
          (hnodes (m + 1) (by omega)).1),
        (hQnode i).2.2.trans (max_le (hnodes m (by omega)).2 (hnodes (m + 1) (by omega)).2),
        hmono _ _ (hQnode i).1 (hinter m (by omega))⟩

end
