-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB198_single_uniform_grid_weighted_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:08:18.371572+00:00
-- url     : https://prove2.me/submissions/685da024-a491-4ffe-a1b2-1d208d6e5402

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gb83_weighted_block_refinement
import Theorems.Thm_AvramDividend_Classical_avram_gb86_uniform_refinement_nnreal_time_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (n m b : ℕ) (hb : 0 < b) (H : ℕ → Ω → ℝ) :
    let δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
    let N : ℕ := (m + 1) * b
    let ε : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let r : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * ε
    ∀ ω, (Finset.range (m + 1)).sum (fun i =>
      H i ω * (X (s i + δ) ω - X (s i) ω - (δ : ℝ) * c)) =
      (Finset.range N).sum (fun j =>
        H (j / b) ω * (X (r j + ε) ω - X (r j) ω -
          (ε : ℝ) * c)) := by
  intro δ s N ε r ω
  let f : ℕ → ℝ := fun j => X (r j) ω - (r j : ℝ) * c
  have hBridge (i : ℕ) : s i = r (i * b) := by
    exact avram_gb86_uniform_refinement_nnreal_time_bridge n m b i hb
  have hCoarseStep (i : ℕ) : s (i + 1) = s i + δ := by
    dsimp only [s]
    push_cast
    ring
  have hFineStep (j : ℕ) : r (j + 1) = r j + ε := by
    dsimp only [r]
    push_cast
    ring
  have hCoarse (i : ℕ) :
      f ((i + 1) * b) - f (i * b) =
        X (s i + δ) ω - X (s i) ω - (δ : ℝ) * c := by
    dsimp only [f]
    rw [← hBridge (i + 1), ← hBridge i, hCoarseStep i]
    push_cast
    ring
  have hFine (j : ℕ) :
      f (j + 1) - f j =
        X (r j + ε) ω - X (r j) ω - (ε : ℝ) * c := by
    dsimp only [f]
    rw [hFineStep j]
    push_cast
    ring
  have hRegroup :=
    avram_gb83_weighted_block_refinement m b hb f (fun i => H i ω)
  calc
    (Finset.range (m + 1)).sum (fun i =>
        H i ω * (X (s i + δ) ω - X (s i) ω - (δ : ℝ) * c)) =
      (Finset.range (m + 1)).sum (fun i =>
        H i ω * (f ((i + 1) * b) - f (i * b))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hCoarse i]
    _ = (Finset.range N).sum (fun j =>
        H (j / b) ω * (f (j + 1) - f j)) := by
          simpa only [N] using hRegroup
    _ = (Finset.range N).sum (fun j =>
        H (j / b) ω * (X (r j + ε) ω - X (r j) ω -
          (ε : ℝ) * c)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hFine j]

