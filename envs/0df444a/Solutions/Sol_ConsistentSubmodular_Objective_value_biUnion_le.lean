-- Prove2me | solution 1 for ConsistentSubmodular.Objective.value_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:19.880043+00:00
-- url     : https://prove2.me/submissions/811aebbc-d06a-4de8-aa04-c5194d261182

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (Q : Finset (Fin n)) {d : ℕ} (cores : Fin d → Finset (Fin n))
    (I : Finset (Fin d)) :
    f.value (Q ∪ I.biUnion cores) ≤ f.value Q + ∑ i ∈ I, (f.value (Q ∪ cores i) - f.value Q) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hdr := f.diminishing_returns (Finset.subset_union_left : Q ⊆ Q ∪ I.biUnion cores)
      (cores i)
    have hset : Q ∪ (cores i ∪ I.biUnion cores) = (Q ∪ I.biUnion cores) ∪ cores i := by
      ext e
      simp only [Finset.mem_union]
      tauto
    rw [hset]
    linarith

end
