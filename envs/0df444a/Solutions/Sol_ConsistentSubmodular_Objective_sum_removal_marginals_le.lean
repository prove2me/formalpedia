-- Prove2me | solution 1 for ConsistentSubmodular.Objective.sum_removal_marginals_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:55.865865+00:00
-- url     : https://prove2.me/submissions/2f2c4f7d-da20-4355-a384-9577f66509bb

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

theorem removal_marginal_le {A B : Finset (Fin n)} (hAB : A ⊆ B)
    {e : Fin n} (he : e ∈ A) :
    f.value B - f.value (B.erase e) ≤ f.value A - f.value (A.erase e) := by
  have h := f.diminishing_returns (Finset.erase_subset_erase e hAB) {e}
  simpa [Finset.union_singleton, Finset.insert_erase he,
    Finset.insert_erase (hAB he)] using h

end ConsistentSubmodular.Objective

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (A : Finset (Fin n)) :
    (∑ e ∈ A, (f.value A - f.value (A.erase e))) ≤ f.value A - f.value ∅ := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have hsum : (∑ e ∈ A,
        (f.value (insert a A) - f.value ((insert a A).erase e))) ≤
        ∑ e ∈ A, (f.value A - f.value (A.erase e)) := by
      exact Finset.sum_le_sum (fun e he =>
        f.removal_marginal_le (Finset.subset_insert a A) he)
    linarith

end
