-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB96_two_mesh_squared_step_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:07:58.147296+00:00
-- url     : https://prove2.me/submissions/7b3479f1-1c34-4082-a864-15a6969ef11d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB91_one_mesh_step_indicator_refinement
import Theorems.Thm_AvramDividend_Classical_avram_gbB92_same_grid_step_product_diagonal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} (n m p : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ) :
    let N : ℕ := (m + 1) * (p + 1)
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    ∀ t ∈ Ioo (0 : ℝ) (n : ℝ), ∀ ω : Ω,
      (K m t ω - K p t ω) ^ 2 =
        (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then (G m (r / (p + 1)) ω -
                G p (r / (m + 1)) ω) ^ 2
          else 0) := by
  intro N δ K t ht ω
  have hb₁ : 0 < p + 1 := Nat.succ_pos p
  have hb₂ : 0 < m + 1 := Nat.succ_pos m
  have hδ : 0 < δ := by dsimp [δ, N]; positivity
  let H : ℕ → ℝ := fun r => G m (r / (p + 1)) ω
  let J : ℕ → ℝ := fun r => G p (r / (m + 1)) ω
  have h₁ : K m t ω =
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then H r else 0) := by
    exact
      (avram_gbB91_one_mesh_step_indicator_refinement
        n m (p + 1) hn hb₁ (G m) t ht ω)
  have h₂ : K p t ω =
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then J r else 0) := by
    convert (avram_gbB91_one_mesh_step_indicator_refinement
      n p (m + 1) hn hb₂ (G p) t ht ω) using 1 <;>
      simp [K, N, δ, J, Nat.mul_comm]
  have hdiff : K m t ω - K p t ω =
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then H r - J r else 0) := by
    rw [h₁, h₂, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> ring
  have hDiag :=
    avram_gbB92_same_grid_step_product_diagonal
      N δ t hδ
      (fun r => H r - J r)
      (fun r => H r - J r)
  rw [hdiff]
  simpa only [pow_two, H, J] using hDiag
