-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.value_union_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:04.313793+00:00
-- url     : https://prove2.me/submissions/e9749f44-7a55-4395-a862-845a230c9246

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ} (f : Objective n)

theorem solution (A X : Finset (Fin n)) (h : ∀ e ∈ A, f.value {e} ≤ f.value ∅) :
    f.value (A ∪ X) ≤ f.value X := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert e A he ih =>
    have hsub := f.submodular {e} (A ∪ X)
    have hmono := f.monotone ∅ ({e} ∩ (A ∪ X)) (Finset.empty_subset _)
    have heq : insert e A ∪ X = {e} ∪ (A ∪ X) := by
      rw [Finset.insert_eq, Finset.union_assoc]
    have he' := h e (Finset.mem_insert_self e A)
    have ih' := ih fun e' he' => h e' (Finset.mem_insert_of_mem he')
    rw [heq]
    linarith

end
