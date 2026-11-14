-- Prove2me | solution 1 for ConsistentSubmodular.intervalSelectionReduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:40.374203+00:00
-- url     : https://prove2.me/submissions/d7338a60-4b28-4c18-926b-4d184ff25b37

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_candidates_of_degenerate
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_candidates_of_gap_pos
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_isAdditionRobust_of_candidates

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Minimax

variable {m : ℕ}

section Window

variable {n : ℕ} (W : WindowInstance n)

/-- The stage-`0` benchmark `f(O_0 ∪ R_0)` is `f(O_0)`. -/
theorem benchmark_zero : W.benchmark 0 = W.objective.value (W.candidate 0) := by
  simp [WindowInstance.benchmark, W.arrivals_zero]

end Window

end ConsistentSubmodular.Minimax

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.IntervalSelection

section Window

variable {n : ℕ} (W : WindowInstance n)

theorem isSimplex_vertex (i : Fin (W.lastStage + 1)) : IsSimplex (vertex i) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold vertex
    split_ifs <;> norm_num
  · simp [vertex]

/-- The degenerate case `κ = 0`: every candidate is empty, so returning
`O_0 = ∅` achieves the benchmark `f(R_j)` exactly. -/
theorem candidates_of_budget_zero {α : ℝ} (hα1 : α ≤ 1) (hκ : W.coreBudget = 0) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  have hempty : ∀ i, W.candidate i = ∅ := fun i =>
    Finset.card_eq_zero.mp (Nat.le_zero.mp (hκ ▸ W.candidate_card i))
  refine ⟨vertex 0, isSimplex_vertex W 0, fun j => ?_⟩
  have hsum : ∑ i, vertex 0 i * W.objective.value (W.candidate i ∪ W.arrivals j) =
      W.objective.value (W.candidate 0 ∪ W.arrivals j) := by
    simp [vertex]
  rw [hsum]
  unfold WindowInstance.benchmark
  rw [hempty j, hempty 0]
  exact mul_le_of_le_one_left (W.objective.nonnegative _) hα1

end Window

/-- **Lemma 2**, with a distribution over the candidates `O_0, ..., O_m`. -/
theorem candidates_of_gap {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap) {n : ℕ}
    (W : WindowInstance n) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  rcases Nat.eq_zero_or_pos W.coreBudget with hκ | hκ
  · exact candidates_of_budget_zero W hα1 hκ
  by_cases h0 : W.objective.value (W.candidate 0) ≤ 0
  · exact candidates_of_degenerate W hα1 (by rw [Minimax.benchmark_zero]; exact h0)
  · push Not at h0
    exact candidates_of_gap_pos W hα0 hgap hκ h0

/-- **Lemma 2** (from interval selection to addition robustness). -/
theorem intervalSelectionReduction : IntervalSelectionReductionGoal := by
  intro α hα0 hα1 hgap n W
  obtain ⟨p, hp, h⟩ := candidates_of_gap hα0 hα1 hgap W
  exact isAdditionRobust_of_candidates hp h

end ConsistentSubmodular.IntervalSelection

end

end

section

open ConsistentSubmodular

theorem solution : IntervalSelectionReductionGoal :=
  IntervalSelection.intervalSelectionReduction

end
