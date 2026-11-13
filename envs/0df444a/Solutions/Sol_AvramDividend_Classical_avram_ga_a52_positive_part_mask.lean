-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a52_positive_part_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:50:29.361355+00:00
-- url     : https://prove2.me/submissions/19effc13-1521-44be-8351-193cf5dbe400

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
    (f : ℕ → Ω → ℝ) :
    ∀ m : ℕ,
      (fun ω => max (if 0 < ρ ω then f m ω else 0) (0 : ℝ)) =
      (fun ω => if 0 < ρ ω then max (f m ω) (0 : ℝ) else 0) := by
  intro m
  funext ω
  by_cases hp : 0 < ρ ω <;> simp [hp]
