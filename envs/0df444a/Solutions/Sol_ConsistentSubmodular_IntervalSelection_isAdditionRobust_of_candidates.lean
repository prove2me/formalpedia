-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.isAdditionRobust_of_candidates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:27.41845+00:00
-- url     : https://prove2.me/submissions/56f7929d-40e4-43f1-975c-1ca123aa38c9

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open ConsistentSubmodular

theorem solution {α : ℝ} {n : ℕ} {W : WindowInstance n}
    {p : Point W.lastStage} (hp : IsSimplex p)
    (h : ∀ j, α * W.benchmark j ≤
      ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j)) :
    ∃ w, W.IsAdditionRobust α w := by
  classical
  refine ⟨fun S => ∑ i, if W.candidate i = S then p i else 0, fun S => ?_, ?_, fun S hS => ?_,
    fun j => ?_⟩
  · exact Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact hp.1 i
      · exact le_rfl
  · rw [Finset.sum_comm]
    simp [hp.2]
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
    have hiS : W.candidate i = S := by
      by_contra hne
      simp [hne] at hi
    subst hiS
    exact ⟨W.candidate_subset i, W.candidate_card i⟩
  · refine (h j).trans_eq ?_
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [ite_mul]

end
