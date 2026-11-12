-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb82_uniform_refinement_linear_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:37:22.065514+00:00
-- url     : https://prove2.me/submissions/4e480e3e-9aab-4143-ba45-0f0c913893c9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb87_uniform_original_time_ledger_regroup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (G : ℕ → ℕ → Ω → ℝ) :
    ∀ m p ω,
      let L : ℕ → Ω → ℝ := fun k η =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        (Finset.range (k + 1)).sum (fun i => G k i η *
          (X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c))
      let N : ℕ := (m + 1) * (p + 1)
      let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      L m ω - L p ω =
        (Finset.range N).sum (fun r =>
          (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω) *
            (X.X (s r + Δ) ω - X.X (s r) ω - (Δ : ℝ) * X.c)) := by
  classical
  intro m p ω
  dsimp only
  have hm := avram_gb87_uniform_original_time_ledger_regroup n m
    (p + 1) (by omega) (fun t => X.X t ω) X.c (fun i => G m i ω)
  have hp := avram_gb87_uniform_original_time_ledger_regroup n p
    (m + 1) (by omega) (fun t => X.X t ω) X.c (fun i => G p i ω)
  dsimp only at hm hp
  rw [hm]
  rw [Nat.mul_comm (p + 1) (m + 1)] at hp
  rw [hp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring
