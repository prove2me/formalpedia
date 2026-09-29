-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_hard_lower_of_tradeoff
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:05:43.999176+00:00
-- url     : https://prove2.me/submissions/c902983d-079a-4c0c-987c-702ac361d947

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_tradeoff_analytic

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem pmMinimaxRegret_zero' {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] (G : PartialMonitoringGame k d 𝕊) :
    pmMinimaxRegret G 0 = 0 := by
  simp [pmMinimaxRegret, pmRegret]

theorem partial_monitoring_hard_lower_of_tradeoff
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (htrade : ∃ ε C δ : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ x : ℝ, 0 ≤ x ∧
        ε / 2 * x +
            (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
              Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≤
          2 * pmMinimaxRegret G n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ pmMinimaxRegret G n := by
  obtain ⟨ε, C, δ, hε, hC, hδ, htrade⟩ := htrade
  obtain ⟨c₀, hc₀, han⟩ :=
    partial_monitoring_hard_tradeoff_analytic ε C δ hε hC hδ
  refine ⟨c₀ / 2, div_pos hc₀ (by norm_num), ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [pmMinimaxRegret_zero']
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨x, hx, hupper⟩ := htrade n hn1
    have hlower := han n hn1 x hx
    linarith

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (htrade : ∃ ε C δ : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ x : ℝ, 0 ≤ x ∧
        ε / 2 * x +
            (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
              Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≤
          2 * BanditAlgorithm.pmMinimaxRegret G n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
        BanditAlgorithm.pmMinimaxRegret G n :=
  BanditAlgorithm.partial_monitoring_hard_lower_of_tradeoff G htrade
