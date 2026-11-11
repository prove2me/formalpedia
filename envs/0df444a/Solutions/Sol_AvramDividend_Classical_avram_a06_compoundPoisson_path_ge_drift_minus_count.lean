-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoisson_path_ge_drift_minus_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:16:55.781651+00:00
-- url     : https://prove2.me/submissions/ff3c5f5e-5e93-418c-b485-124f43f3f40e

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Each jump is at least -1, so the sum of jumps is bounded below
by the negative of the number of arrivals. -/
theorem solution
    {Ω : Type*} (b : ℝ) (τ Y : ℕ → Ω → ℝ) (ω : Ω)
    (hmarks : ∀ n, -1 ≤ Y n ω) (t : ℝ) :
    b * t - (LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t : ℝ) ≤
      LevyFoundations.compoundPoisson b τ Y t ω := by
  let N := LevyFoundations.jumpCount
    (fun n => LevyFoundations.arrival τ n ω) t
  have hsum :
      (∑ n ∈ Finset.range N, (-1 : ℝ)) ≤
        (∑ n ∈ Finset.range N, Y n ω) :=
    Finset.sum_le_sum (fun n _ => hmarks n)
  have hone : (∑ n ∈ Finset.range N, (-1 : ℝ)) = -(N : ℝ) := by
    simp
  rw [hone] at hsum
  change b * t - (N : ℝ) ≤
    (0 : ℝ) + b * t + (∑ n ∈ Finset.range N, Y n ω)
  linarith
