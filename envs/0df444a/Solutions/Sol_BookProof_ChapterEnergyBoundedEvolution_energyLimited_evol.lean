-- Prove2me | solution 1 for BookProof.ChapterEnergyBoundedEvolution.energyLimited_evol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:38:20.699106+00:00
-- url     : https://prove2.me/submissions/3ece00fb-e7ef-4310-b5cb-eb69492b77b9

-- Generated from ChapterEnergyBoundedEvolution.lean — solution of BookProof.ChapterEnergyBoundedEvolution.energyLimited_evol
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
open BookProof.ChapterEnergyBoundedEvolution




open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {Emax : ℝ} (t : ℝ) (h : EnergyLimited E μ Emax f) :
    EnergyLimited E μ Emax (evol E t f) := by

  filter_upwards [h] with x hx hne
  refine hx fun hf => hne ?_
  simp [evol, hf]
