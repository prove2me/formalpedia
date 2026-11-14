-- Prove2me | solution 1 for ConsistentSubmodular.Minimax.minimax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:21.814687+00:00
-- url     : https://prove2.me/submissions/eb65de1e-13b6-47d0-8c93-0a583c6b1edb

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax
import Theorems.Thm_ConsistentSubmodular_Minimax_saddlePoint
import Theorems.Thm_ConsistentSubmodular_Minimax_guarantee_le_rowMax

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
open ConsistentSubmodular ConsistentSubmodular.Minimax
variable {m : ℕ}
variable {n : ℕ} (W : WindowInstance n)

theorem solution : MinimaxGoal := by
  intro n W _ h0
  have hpos : ∀ j, 0 < W.benchmark j := fun j =>
    lt_of_lt_of_le (by rw [benchmark_zero]; exact h0) (benchmark_zero_le W j)
  have hw0 : ∀ i j, 0 ≤ W.payoff i j := fun i j =>
    div_nonneg (W.objective.nonnegative _) (hpos j).le
  have hw1 : ∀ i j, W.payoff i j ≤ 1 := fun i j => by
    rw [WindowInstance.payoff, div_le_one (hpos j)]
    exact W.candidate_optimal j (W.candidate i) (W.candidate_subset i) (W.candidate_card i)
  obtain ⟨v, ⟨a, ha, hav⟩, ⟨b, hb, hbv⟩⟩ := saddlePoint W.payoff
  have hga : v ≤ guarantee W.payoff a := Finset.le_inf' _ _ fun j _ => hav j
  have hrb : rowMax W.payoff b ≤ v := Finset.sup'_le _ _ fun i _ => hbv i
  have hweak := guarantee_le_rowMax W.payoff ha hb
  -- A distribution `α` meets a level `ρ` of the linear program at every stage
  -- exactly when `ρ ≤ min_j Σ_i α_i w_{i,j}`.
  have hfeas : ∀ (α : Point W.lastStage) (ρ : ℝ), (∀ j, ρ * W.benchmark j ≤
      ∑ i, α i * W.objective.value (W.candidate i ∪ W.arrivals j)) ↔
        ρ ≤ guarantee W.payoff α := by
    intro α ρ
    unfold guarantee
    rw [Finset.le_inf'_iff]
    refine forall_congr' fun j => ?_
    rw [sum_mul_payoff, le_div_iff₀ (hpos j)]
    simp
  have hv0 : 0 ≤ v :=
    (Finset.sum_nonneg fun j _ => mul_nonneg (hb.1 j) (hw0 0 j)).trans (hbv 0)
  have hv1 : v ≤ 1 := by
    calc v ≤ ∑ i, a i * W.payoff i 0 := hav 0
      _ ≤ ∑ i, a i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hw1 i 0) (ha.1 i)
      _ = 1 := by rw [← Finset.sum_mul, ha.2, one_mul]
  have hlp : W.lpValue = v := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨hv0, hv1, a, ha, (hfeas a v).mpr hga⟩, ?_⟩
    rintro ρ ⟨-, -, α, hα, hρ⟩
    exact ((hfeas α ρ).mp hρ).trans ((guarantee_le_rowMax W.payoff hα hb).trans hrb)
  rw [hlp]
  refine ⟨⟨⟨a, ha, le_antisymm hga (hweak.trans hrb)⟩, ?_⟩,
    ⟨⟨b, hb, le_antisymm (hga.trans hweak) hrb⟩, ?_⟩⟩
  · rintro x ⟨α, hα, rfl⟩
    exact (guarantee_le_rowMax W.payoff hα hb).trans hrb
  · rintro x ⟨β, hβ, rfl⟩
    exact hga.trans (guarantee_le_rowMax W.payoff ha hβ)

end
