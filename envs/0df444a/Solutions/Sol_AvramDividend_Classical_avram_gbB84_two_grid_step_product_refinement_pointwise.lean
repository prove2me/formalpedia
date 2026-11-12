-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB84_two_grid_step_product_refinement_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:07:27.065837+00:00
-- url     : https://prove2.me/submissions/c4b465c5-7d28-43e0-8e40-3819554e6413

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB91_one_mesh_step_indicator_refinement
import Theorems.Thm_AvramDividend_Classical_avram_gbB92_same_grid_step_product_diagonal
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} (n m l : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ) :
    let N : ℕ := (m + 1) * (l + 1)
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    ∀ t ∈ Ioo (0 : ℝ) (n : ℝ), ∀ ω : Ω,
      K m t ω * K l t ω =
        (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then G m (r / (l + 1)) ω * G l (r / (m + 1)) ω
          else 0) := by
  intro N δ K t ht ω
  have hb₁ : 0 < l + 1 := Nat.succ_pos l
  have hb₂ : 0 < m + 1 := Nat.succ_pos m
  have hδ : 0 < δ := by dsimp [δ, N]; positivity
  have h₁ : K m t ω =
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then G m (r / (l + 1)) ω else 0) := by
    exact
      (avram_gbB91_one_mesh_step_indicator_refinement
        n m (l + 1) hn hb₁ (G m) t ht ω)
  have h₂ : K l t ω =
      (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then G l (r / (m + 1)) ω else 0) := by
    convert (avram_gbB91_one_mesh_step_indicator_refinement
      n l (m + 1) hn hb₂ (G l) t ht ω) using 1 <;>
      simp [K, N, δ, Nat.mul_comm]
  rw [h₁, h₂]
  exact avram_gbB92_same_grid_step_product_diagonal
    N δ t hδ
    (fun r => G m (r / (l + 1)) ω)
    (fun r => G l (r / (m + 1)) ω)
