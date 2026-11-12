-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb22_compact_clock_le_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:25:41.35891+00:00
-- url     : https://prove2.me/submissions/00895bce-f533-4a45-b5e0-8d3493ed2c6f

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- Spatial clipping by a finite clock preserves its horizon bound. -/
theorem solution
    {Ω : Type*} (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (ξ : ℕ → Ω → ℝ≥0∞) (κ : ℕ → Ω → ℝ≥0)
    (hκ : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞) (ξ k ω)).toNNReal) :
    ∀ k ω, κ k ω ≤ (n : ℝ≥0) := by
  intro k ω
  have hmin : (min (ρ ω : ℝ≥0∞) (ξ k ω)).toNNReal ≤ ρ ω := by
    have h := ENNReal.toNNReal_mono (show (ρ ω : ℝ≥0∞) ≠ ⊤ by simp)
      (min_le_left (ρ ω : ℝ≥0∞) (ξ k ω))
    simpa using h
  rw [hκ k ω]
  exact hmin.trans (hρbound ω)
