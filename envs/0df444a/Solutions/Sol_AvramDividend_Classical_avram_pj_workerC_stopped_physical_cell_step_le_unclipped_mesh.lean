-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_stopped_physical_cell_step_le_unclipped_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:35:51.743758+00:00
-- url     : https://prove2.me/submissions/f47e356c-fc07-4c26-b764-3142266f2606

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (g : ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (Δ : ℝ≥0) (hStep : ∀ i, g (i+1) ≤ g i + Δ) :
    ∀ ω i, min (g (i+1)) (ρ ω) ≤ min (g i) (ρ ω) + Δ := by
  intro ω i
  rcases le_total (g i) (ρ ω) with hi | hr
  · rw [min_eq_left hi]
    exact (min_le_left _ _).trans (hStep i)
  · rw [min_eq_right hr]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (by positivity))
