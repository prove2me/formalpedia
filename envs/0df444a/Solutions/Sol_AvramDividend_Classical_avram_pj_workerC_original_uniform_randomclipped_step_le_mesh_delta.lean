-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_uniform_randomclipped_step_le_mesh_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:51:26.221862+00:00
-- url     : https://prove2.me/submissions/e425fc98-3676-4d5c-9963-52f0126d550c

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_stopped_physical_cell_step_le_unclipped_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} (n m : ℕ) (ρ : Ω → ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : Ω → ℕ → ℝ≥0 := fun ω i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    ∀ ω i, u ω (i + 1) ≤ u ω i + Δ := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let g : ℕ → ℝ≥0 := fun i =>
    ((min i (m + 1) : ℕ) : ℝ≥0) * Δ
  have hStep : ∀ i, g (i + 1) ≤ g i + Δ := by
    intro i
    change (((min (i + 1) (m + 1) : ℕ) : ℝ≥0) * Δ) ≤
      (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) + Δ
    have hn : min (i + 1) (m + 1) ≤ min i (m + 1) + 1 := by omega
    have hc : ((min (i + 1) (m + 1) : ℕ) : ℝ≥0) ≤
        ((min i (m + 1) : ℕ) : ℝ≥0) + 1 := by
      exact_mod_cast hn
    calc
      _ ≤ (((min i (m + 1) : ℕ) : ℝ≥0) + 1) * Δ :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  change ∀ ω i, min (g (i + 1)) (ρ ω) ≤ min (g i) (ρ ω) + Δ
  exact avram_pj_workerC_stopped_physical_cell_step_le_unclipped_mesh
    g ρ Δ hStep
