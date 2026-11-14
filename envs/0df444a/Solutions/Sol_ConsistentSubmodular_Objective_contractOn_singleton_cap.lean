-- Prove2me | solution 1 for ConsistentSubmodular.Objective.contractOn_singleton_cap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:21.125073+00:00
-- url     : https://prove2.me/submissions/cbb92615-2933-4c98-877f-1e9b7f73a980

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

/-- Contraction by any additional buffer only decreases the remaining
singleton marginals certified by a forced set. -/
theorem forced_marginal_under_buffer (D Q : Finset (Fin n)) (e : Fin n) {c : ℝ}
    (h : f.value (insert e D) - f.value D ≤ c) :
    f.value (insert e (D ∪ Q)) - f.value (D ∪ Q) ≤ c := by
  have hdec := f.diminishing_returns (Finset.subset_union_left : D ⊆ D ∪ Q) {e}
  simp only [Finset.union_singleton] at hdec
  exact hdec.trans h

end ConsistentSubmodular.Objective

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (U D Q : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (hcap : ∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c) :
    ∀ e, (f.contractOn U (D ∪ Q)).value {e} - (f.contractOn U (D ∪ Q)).value ∅ ≤ c := by
  intro e
  rw [contractOn_empty, sub_zero]
  by_cases heU : e ∈ U
  · have hint : {e} ∩ U = {e} := Finset.inter_eq_left.mpr (by simpa using heU)
    change f.value ((D ∪ Q) ∪ ({e} ∩ U)) - f.value (D ∪ Q) ≤ c
    rw [hint, Finset.union_singleton]
    by_cases heD : e ∈ D
    · simp [Finset.mem_union_left Q heD, hc]
    · exact f.forced_marginal_under_buffer D Q e (hcap e heU heD)
  · have hint : {e} ∩ U = ∅ := by simp [heU]
    simpa [contractOn, hint] using hc

end
