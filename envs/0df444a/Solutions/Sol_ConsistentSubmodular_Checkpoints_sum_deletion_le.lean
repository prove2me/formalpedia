-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.sum_deletion_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:00.650436+00:00
-- url     : https://prove2.me/submissions/1891db89-52ad-4d61-9844-3891566a2fb3

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Checkpoints_marginal_le

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem solution (f : Objective n) (A : Finset (Fin n)) :
    ∑ e ∈ A, (f.value A - f.value (A.erase e)) ≤ f.value A - f.value ∅ := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have hterm : ∀ e ∈ B, f.value (insert a B) - f.value ((insert a B).erase e) ≤
        f.value B - f.value (B.erase e) := by
      intro e he
      have hsub : B.erase e ⊆ (insert a B).erase e :=
        Finset.erase_subset_erase e (Finset.subset_insert a B)
      have h := marginal_le f hsub e
      rwa [Finset.insert_erase (Finset.mem_insert_of_mem he), Finset.insert_erase he] at h
    have hsum := Finset.sum_le_sum hterm
    linarith

end
