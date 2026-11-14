-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.candidates_of_gap_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:49.760619+00:00
-- url     : https://prove2.me/submissions/274ac509-2dd5-4df2-b658-30ad765aeb49

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Minimax_minimax
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_le_rowMax_payoff

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

/-- Optimality and monotonicity: `f(O_j ∪ R_j) ≥ f(O_0 ∪ R_j) ≥ f(O_0)`. -/
theorem benchmark_zero_le (j : Fin (W.lastStage + 1)) : W.benchmark 0 ≤ W.benchmark j := by
  have hopt := W.candidate_optimal j (W.candidate 0) (W.candidate_subset 0) (W.candidate_card 0)
  have hsub : W.candidate 0 ∪ W.arrivals 0 ⊆ W.candidate 0 ∪ W.arrivals j := by
    rw [W.arrivals_zero]
    exact Finset.union_subset_union (subset_refl _) (Finset.empty_subset _)
  have hmono := W.objective.monotone _ _ hsub
  unfold WindowInstance.benchmark
  linarith

/-- `Σ_i a_i w_{i,j} = Σ_i a_i f(O_i ∪ R_j) / f(O_j ∪ R_j)`. -/
theorem sum_mul_payoff (a : Point W.lastStage) (j : Fin (W.lastStage + 1)) :
    ∑ i, a i * W.payoff i j =
      (∑ i, a i * W.objective.value (W.candidate i ∪ W.arrivals j)) / W.benchmark j := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

end Window

end ConsistentSubmodular.Minimax

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.IntervalSelection
variable {n : ℕ} (W : WindowInstance n)

theorem solution {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap)
    (hκ : 1 ≤ W.coreBudget) (h0 : 0 < W.objective.value (W.candidate 0)) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  have hpos : ∀ j, 0 < W.benchmark j := fun j =>
    lt_of_lt_of_le (by rw [Minimax.benchmark_zero]; exact h0) (Minimax.benchmark_zero_le W j)
  obtain ⟨⟨⟨a, ha, haρ⟩, -⟩, ⟨⟨b, hb, hbρ⟩, -⟩⟩ := Minimax.minimax n W hκ h0
  -- `ρ⋆ = min_β max_i Σ_j β_j w_{i,j} ≥ α`.
  have hρ : α ≤ W.lpValue := by
    rw [hbρ]
    exact le_rowMax_payoff W hα0 hgap hpos b hb
  refine ⟨a, ha, fun j => ?_⟩
  -- `ρ⋆ = min_j Σ_i a_i w_{i,j} ≤ Σ_i a_i w_{i,j}`.
  have hcol : W.lpValue ≤ ∑ i, a i * W.payoff i j := by
    rw [haρ]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  rw [Minimax.sum_mul_payoff, le_div_iff₀ (hpos j)] at hcol
  exact (mul_le_mul_of_nonneg_right hρ (hpos j).le).trans hcol

end
