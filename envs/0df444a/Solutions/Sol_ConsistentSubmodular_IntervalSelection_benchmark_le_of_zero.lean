-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.benchmark_le_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:47.606196+00:00
-- url     : https://prove2.me/submissions/3a0a38ed-3000-4777-b41b-55351756011a

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_value_union_le

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.IntervalSelection
variable {n : ℕ} (W : WindowInstance n)

theorem solution (h0 : W.benchmark 0 ≤ 0) (j : Fin (W.lastStage + 1)) :
    W.benchmark j ≤ W.objective.value (W.arrivals j) := by
  have hO0 : W.objective.value (W.candidate 0) ≤ 0 := by
    simpa [WindowInstance.benchmark, W.arrivals_zero] using h0
  have hsingle : ∀ e ∈ W.candidate j, W.objective.value {e} ≤ W.objective.value ∅ := by
    intro e he
    have hcard : ({e} : Finset (Fin n)).card ≤ W.coreBudget := by
      rw [Finset.card_singleton]
      exact (Finset.card_pos.mpr ⟨e, he⟩).trans_le (W.candidate_card j)
    have hopt := W.candidate_optimal 0 {e}
      (Finset.singleton_subset_iff.mpr (W.candidate_subset j he)) hcard
    rw [W.arrivals_zero, Finset.union_empty, Finset.union_empty] at hopt
    have := W.objective.nonnegative ∅
    linarith
  exact value_union_le W.objective _ _ hsingle

end
