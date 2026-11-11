-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoissonStartsZeroAE_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:29:29.7592+00:00
-- url     : https://prove2.me/submissions/785e20fe-92d6-4ac6-bec9-3a0375e0ea04

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive
import Theorems.Thm_levy_foundations_piecewisePathAtZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
noncomputable section

/-- The canonical compound-Poisson sample path starts at zero almost surely. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' P)
    (hr : 0 < r) (b : ℝ) :
    ∀ᵐ ω ∂P, LevyFoundations.compoundPoisson b τ Y 0 ω = 0 := by
  filter_upwards [levy_foundations_compoundDriverInterarrivalPositive hd hr]
    with ω hpos
  change LevyFoundations.piecewisePath 0 b
    (fun n => LevyFoundations.arrival τ n ω) (fun n => Y n ω) 0 = 0
  have hfirst : 0 < LevyFoundations.arrival τ 0 ω := by
    simpa [LevyFoundations.arrival] using hpos 0
  exact levy_foundations_piecewisePathAtZero hfirst