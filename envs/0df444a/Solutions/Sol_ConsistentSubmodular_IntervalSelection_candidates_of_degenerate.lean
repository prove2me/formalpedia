-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.candidates_of_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:43.237254+00:00
-- url     : https://prove2.me/submissions/189e0723-d5c0-4c8c-8f03-98f3e874f545

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_benchmark_le_of_zero

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

end Window

end ConsistentSubmodular.IntervalSelection

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.IntervalSelection
variable {n : ℕ} (W : WindowInstance n)

theorem solution {α : ℝ} (hα1 : α ≤ 1) (h0 : W.benchmark 0 ≤ 0) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  refine ⟨vertex 0, isSimplex_vertex W 0, fun j => ?_⟩
  have hsum : ∑ i, vertex 0 i * W.objective.value (W.candidate i ∪ W.arrivals j) =
      W.objective.value (W.candidate 0 ∪ W.arrivals j) := by
    simp [vertex]
  rw [hsum]
  have h1 := benchmark_le_of_zero W h0 j
  have h2 := W.objective.monotone (W.arrivals j) (W.candidate 0 ∪ W.arrivals j)
    Finset.subset_union_right
  have h3 := mul_le_of_le_one_left (W.objective.nonnegative (W.candidate j ∪ W.arrivals j)) hα1
  unfold WindowInstance.benchmark at h1 h3 ⊢
  linarith

end
