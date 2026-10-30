-- Prove2me | solution 1 for AvgRewardPMD.SPMD.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:30:10.33809+00:00
-- url     : https://prove2.me/submissions/2c388255-70dc-4e6e-9f2b-b4ea66d1a4a2

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Theorems.Thm_AvgRewardPMD_SPMD_bellman_solution_sets
import Theorems.Thm_AvgRewardPMD_SPMD_avg_cost_eq_stationary

open FoundationsML.ReinforcementLearning AvgRewardPMD.SPMD

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (hmix : IsMixing P)
    (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (ν' : S → ℝ)
    (hν' : MarkovMixing.IsStationary (stateMatrix P π') ν') (s₀ : S) :
    avgCost P π' (fun s a => c s a + h s (π' s)) s₀ - avgCost P π (fun s a => c s a + h s (π s)) s₀
      = ∑ s, ν' s * (∑ a, diffQ P π (fun s a => c s a + h s (π s)) (s, a) * (π' s a - π s a)
          + h s (π' s) - h s (π s)) := by
  set cπ : S → A → ℝ := fun s a => c s a + h s (π s) with hcπ
  set cπ' : S → A → ℝ := fun s a => c s a + h s (π' s) with hcπ'
  set Qb := diffQ P π cπ with hQb
  obtain ⟨ν, hν, -⟩ := (Classical.choose_spec hmix) π hπ
  have hρ : ∀ s, avgCost P π cπ s = avgCost P π cπ s₀ := by
    intro s
    rw [(avg_cost_eq_stationary P hP hmix π hπ ν hν cπ s).2,
      (avg_cost_eq_stationary P hP hmix π hπ ν hν cπ s₀).2]
  set ρ := avgCost P π cπ s₀ with hρdef
  have hρ' : avgCost P π' cπ' s₀ = ∑ s, ν' s * InducedReward π' cπ' s :=
    (avg_cost_eq_stationary P hP hmix π' hπ' ν' hν' cπ' s₀).2
  have hbell : ∀ x : S × A, Qb x = cπ x.1 x.2 - ρ + ∑ y, saTransition P π x y * Qb y := by
    have h2 := (bellman_solution_sets P hP hmix π hπ cπ).2
    have hmem : Qb ∈ {Q : S × A → ℝ | ∃ b : ℝ, Q = fun x => diffQ P π cπ x + b} :=
      ⟨0, by funext x; simp [Qb]⟩
    rw [← h2] at hmem
    intro x
    rw [← hρ x.1]
    exact hmem x
  set V : S → ℝ := fun s => ∑ a, π s a * Qb (s, a) with hV
  have hPQ : ∀ s a, ∑ y, saTransition P π (s, a) y * Qb y = ∑ s'', P s a s'' * V s'' := by
    intro s a
    rw [Fintype.sum_prod_type]
    simp only [saTransition, Matrix.of_apply, V, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s'' _; apply Finset.sum_congr rfl; intro a'' _; ring
  have hstat : ∀ s'', ∑ s, ν' s * ∑ a, π' s a * P s a s'' = ν' s'' := by
    intro s''
    have := congrFun hν'.2 s''
    simpa only [Matrix.vecMul, dotProduct, stateMatrix, Matrix.of_apply, InducedTransition]
      using this
  have hterm : ∀ s, ∑ a, Qb (s, a) * (π' s a - π s a) + h s (π' s) - h s (π s)
      = InducedReward π' cπ' s - ρ + ∑ a, π' s a * ∑ s'', P s a s'' * V s'' - V s := by
    intro s
    have e1 : ∑ a, Qb (s, a) * (π' s a - π s a) = ∑ a, π' s a * Qb (s, a) - V s := by
      simp only [V, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a _; ring
    have e2 : ∑ a, π' s a * Qb (s, a)
        = ∑ a, π' s a * (cπ s a - ρ + ∑ s'', P s a s'' * V s'') := by
      apply Finset.sum_congr rfl; intro a _; rw [hbell (s, a), hPQ s a]
    rw [e1, e2]
    simp only [InducedReward, cπ, cπ', mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, (hπ' s).2]
    ring
  have hmid : ∑ s, ν' s * ∑ a, π' s a * ∑ s'', P s a s'' * V s'' = ∑ s'', ν' s'' * V s'' := by
    calc ∑ s, ν' s * ∑ a, π' s a * ∑ s'', P s a s'' * V s''
        = ∑ s, ∑ s'', ∑ a, ν' s * (π' s a * (P s a s'' * V s'')) := by
          simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ s'', ∑ s, ∑ a, ν' s * (π' s a * (P s a s'' * V s'')) := Finset.sum_comm
      _ = ∑ s'', (∑ s, ν' s * ∑ a, π' s a * P s a s'') * V s'' := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro s'' _
          apply Finset.sum_congr rfl; intro s _
          apply Finset.sum_congr rfl; intro a _
          ring
      _ = ∑ s'', ν' s'' * V s'' := by simp_rw [hstat]
  simp_rw [hterm]
  rw [hρ']
  have hsum1 : ∑ s, ν' s = 1 := hν'.1.2
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hmid]
  rw [← Finset.sum_mul, hsum1]
  ring
