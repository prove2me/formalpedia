-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_forced_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:31.192088+00:00
-- url     : https://prove2.me/submissions/a9f94c4a-e9f4-4771-8259-2449054e734b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Theorems.Thm_ConsistentSubmodular_Objective_sum_removal_marginals_le
import Theorems.Thm_ConsistentSubmodular_Objective_exists_penalized_core

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

theorem solution (U : Finset (Fin n)) (k H : ℕ) (hH : 0 < H) (hHk : H ≤ k)
    (c V : ℝ) (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (hpay : V ≤ (H : ℝ) * c) :
    ∃ D ⊆ U, D.card < H ∧
      ∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c := by
  classical
  obtain ⟨D, hDU, hins, hrem⟩ := f.exists_penalized_core U c
  refine ⟨D, hDU, ?_, hins⟩
  by_contra hcard
  have hHD : H ≤ D.card := le_of_not_gt hcard
  obtain ⟨A, hAD, hAH⟩ := Finset.exists_subset_card_eq hHD
  have hAnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : (∑ e ∈ A, c) < ∑ e ∈ A, (f.value A - f.value (A.erase e)) := by
    exact Finset.sum_lt_sum_of_nonempty hAnonempty (fun e he =>
      (hrem e (hAD he)).trans_le (f.removal_marginal_le hAD he))
  have hsum := f.sum_removal_marginals_le A
  have hval := hscale A (hAD.trans hDU) (by omega)
  have h0 := f.nonnegative ∅
  simp only [Finset.sum_const, nsmul_eq_mul, hAH] at hstrict
  linarith

end
