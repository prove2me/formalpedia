-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoissonCadlagAE_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:11:23.133504+00:00
-- url     : https://prove2.me/submissions/d06072f5-3653-4de2-a7d4-5ae5eef199b7

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_levy_foundations_piecewisePathIsCadlag

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
noncomputable section

/-- A public, source-exact almost-sure càdlàg theorem for the canonical
compound-Poisson driver, using three public Proved prerequisites. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' P)
    (hr : 0 < r) (b : ℝ) :
    ∀ᵐ ω ∂P,
      LevyFoundations.isCadlag
        (fun t => LevyFoundations.compoundPoisson b τ Y t ω) := by
  filter_upwards
    [levy_foundations_compoundDriverArrivalStrictMono hd hr,
      levy_foundations_compoundDriverArrivalDiverges hd hr]
    with ω hmono htop
  exact levy_foundations_piecewisePathIsCadlag hmono htop
