-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a50_mask_zero_clock_unmask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:50:10.122223+00:00
-- url     : https://prove2.me/submissions/f814bc38-d13d-4b4a-aeec-0127d43aeb51

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
    (B : ℕ → Ω → ℝ)
    (hZero : ∀ m ω, ρ ω = 0 → B m ω = 0) :
    (fun m ω => if 0 < ρ ω then B m ω else 0) = B := by
  funext m ω
  by_cases hp : 0 < ρ ω
  · simp [hp]
  · have hz : ρ ω = 0 :=
      le_antisymm (le_of_not_gt hp) bot_le
    simpa [hp] using (hZero m ω hz).symm
