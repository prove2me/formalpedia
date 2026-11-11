-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoisson_path_le_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:51:29.709397+00:00
-- url     : https://prove2.me/submissions/4bbfc8e7-8634-4fe0-ad71-adeb53093091

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Finite sums of negative marks keep the path below its affine drift. -/
theorem solution
    {Ω : Type*} (b : ℝ) (τ Y : ℕ → Ω → ℝ) (ω : Ω)
    (hneg : ∀ n, Y n ω ≤ 0) (t : ℝ) :
    LevyFoundations.compoundPoisson b τ Y t ω ≤ b * t := by
  change ((0 : ℝ) + b * t +
    (∑ n ∈ Finset.range
      (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) t), Y n ω))
    ≤ b * t
  have hsum :
      (∑ n ∈ Finset.range
        (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) t), Y n ω) ≤ 0 := by
    exact Finset.sum_nonpos fun n _ => hneg n
  linarith