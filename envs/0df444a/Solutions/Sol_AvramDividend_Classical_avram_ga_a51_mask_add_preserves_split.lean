-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a51_mask_add_preserves_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:50:19.185192+00:00
-- url     : https://prove2.me/submissions/ccd79350-67b9-4e43-a07c-f56f8b1e6145

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} (ρ : Ω → ℝ≥0)
    (B V T : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, B m ω = V m ω + T m ω) :
    ∀ m ω,
      (if 0 < ρ ω then B m ω else 0) =
      (if 0 < ρ ω then V m ω else 0) +
      (if 0 < ρ ω then T m ω else 0) := by
  intro m ω
  by_cases hp : 0 < ρ ω
  · simpa [hp] using hSplit m ω
  · simp [hp]
