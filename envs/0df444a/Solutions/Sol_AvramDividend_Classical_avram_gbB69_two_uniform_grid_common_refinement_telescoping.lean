-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB69_two_uniform_grid_common_refinement_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:37:17.529244+00:00
-- url     : https://prove2.me/submissions/6430d7ce-bbf2-4be5-a4da-7227af50815a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb87_uniform_original_time_ledger_regroup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal BigOperators

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (n m p : ℕ) (G : ℕ → ℕ → Ω → ℝ) :
    let L : ℕ → Ω → ℝ := fun h ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((h + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (h + 1)).sum (fun i =>
        G h i ω * (X (s i + Δ) ω - X (s i) ω - (Δ : ℝ) * c))
    let N : ℕ := (m + 1) * (p + 1)
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun r => (r : ℝ≥0) * Δ
    ∀ ω, L m ω - L p ω =
      (Finset.range N).sum (fun r =>
        (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω) *
          (X (s r + Δ) ω - X (s r) ω - (Δ : ℝ) * c)) := by
  classical
  dsimp only
  intro ω
  have hm := avram_gb87_uniform_original_time_ledger_regroup n m
    (p + 1) (by omega) (fun t => X t ω) c (fun i => G m i ω)
  have hp := avram_gb87_uniform_original_time_ledger_regroup n p
    (m + 1) (by omega) (fun t => X t ω) c (fun i => G p i ω)
  dsimp only at hm hp
  rw [hm]
  rw [Nat.mul_comm (p + 1) (m + 1)] at hp
  rw [hp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring
